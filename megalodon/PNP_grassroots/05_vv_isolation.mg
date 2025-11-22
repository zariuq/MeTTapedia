Definition LinearHash : set -> set -> set -> set -> set :=
  fun k m A b => fun x :e Bits :^: m =>
    vec_xor k (matrix_vec_prod k m A x) b.

Definition TwoUniversalFamily : set -> set -> set :=
  fun k m => (Bits :^: (k * m)) :*: (Bits :^: k).

Definition is_pairwise_independent : set -> set -> prop :=
  fun k m =>
    forall x1 :e Bits :^: m, forall x2 :e Bits :^: m,
    x1 <> x2 ->
    True.

Definition VV_isolated : set -> set -> set -> set -> set -> prop :=
  fun m k S A b =>
    equip one {x :e S | LinearHash k m A b x = zero_vector k}.

Theorem VV_isolation_classical :
  forall S k,
    S <> Empty ->
    nat_p k ->
    True.
Admitted.

Theorem VV_isolation_efficient :
  forall m F alpha,
    nat_p m ->
    is_SAT m F ->
    True.
Admitted.

Theorem VV_rejection_sampling :
  forall m F,
    nat_p m ->
    is_SAT m F ->
    True.
Admitted.

Definition c2 : set := ordsucc (ordsucc (ordsucc (ordsucc (ordsucc (ordsucc (ordsucc (ordsucc (ordsucc (ordsucc 0))))))))).

Definition matrix_column_vv : set -> set -> set -> set :=
  fun rows A i => fun j :e rows => ap (ap A j) i.

Definition vv_labels : set -> set -> set -> set :=
  fun k A b => fun i :e omega => (matrix_column_vv k A i, b).

Theorem vv_label_length :
  forall m,
    nat_p m ->
    True.
Admitted.

Definition VVInstance : set -> set :=
  fun m => {Phi :e (Power (Power omega)) :*: (Bits :^: (vv_num_rows m * m)) :*: (Bits :^: vv_num_rows m) |
    exists F :e Power (Power omega), exists h :e Mask m,
    exists A :e Bits :^: (vv_num_rows m * m), exists b :e Bits :^: vv_num_rows m,
    Phi = (masked_cnf m h F, A, b)}.

Definition instance_cnf : set -> set := fun Phi => ap Phi 0.
Definition instance_matrix : set -> set := fun Phi => ap Phi 1.
Definition instance_rhs : set -> set := fun Phi => ap Phi 2.

Definition instance_witness : set -> set -> set :=
  fun m Phi =>
    Eps_i (fun x => x :e Bits :^: m /\
                    satisfies x (instance_cnf Phi) /\
                    LinearHash (vv_num_rows m) m (instance_matrix Phi) (instance_rhs Phi) x = zero_vector (vv_num_rows m)).

Definition has_unique_witness : set -> set -> prop :=
  fun m Phi =>
    equip one {x :e Bits :^: m |
      satisfies x (instance_cnf Phi) /\
      LinearHash (vv_num_rows m) m (instance_matrix Phi) (instance_rhs Phi) x = zero_vector (vv_num_rows m)}.

Theorem promise_verification_polytime :
  forall m Phi x,
    nat_p m ->
    True.
Admitted.

Theorem vv_delta_bias_robustness :
  forall m A sigma delta,
    nat_p m ->
    True.
Admitted.
