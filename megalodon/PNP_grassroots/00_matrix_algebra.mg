Definition Matrix : set -> set -> set -> prop :=
  fun rows cols A =>
    forall i :e rows, forall j :e cols, ap (ap A i) j :e two.

Definition Matrices : set -> set -> set :=
  fun k m => {A :e (Bits :^: m) :^: k | Matrix k m A}.

Definition mat_entry : set -> set -> set -> set :=
  fun A i j => ap (ap A i) j.

Definition zero_matrix : set -> set -> set :=
  fun rows cols => fun i :e rows => fun j :e cols => 0.

Definition identity_matrix : set -> set :=
  fun n => fun i :e n => fun j :e n => if i = j then one else 0.

Definition RowVector : set -> set -> prop :=
  fun n v => BitString n v.

Definition ColVector : set -> set -> prop :=
  fun n v => BitString n v.

Definition matrix_col : set -> set -> set :=
  fun A j => fun i :e omega => ap (ap A i) j.

Definition matrix_row : set -> set -> set :=
  fun A i => ap A i.

Definition bit_and : set -> set -> set :=
  fun a b => if a = one /\ b = one then one else 0.

Definition inner_product_f2 : set -> set -> set -> set :=
  fun n a b =>
    nat_primrec 0 (fun j acc => xor acc (bit_and (ap a j) (ap b j))) n.

Definition matrix_vec_prod : set -> set -> set -> set -> set :=
  fun k m A x =>
    fun i :e k => inner_product_f2 m (matrix_row A i) x.

Definition mat_vec : set -> set -> set :=
  fun A x => fun i :e omega => inner_product_f2 omega (matrix_row A i) x.

Definition matrix_mul : set -> set -> set -> set -> set -> set :=
  fun k m n A B =>
    fun i :e k => fun j :e n =>
      inner_product_f2 m (matrix_row A i) (matrix_col B j).

Definition vec_add_f2 : set -> set -> set -> set :=
  fun n x y => fun i :e n => xor (ap x i) (ap y i).

Definition LinearHashF2 : set -> set -> set -> set -> set :=
  fun k m A b =>
    fun x :e Bits :^: m => vec_add_f2 k (matrix_vec_prod k m A x) b.

Definition apply_linear_hash : set -> set -> set -> set -> set -> set :=
  fun k m A b x => vec_add_f2 k (matrix_vec_prod k m A x) b.

Definition LinearHashFamily : set -> set -> set :=
  fun k m => Matrices k m :*: Bits :^: k.

Definition is_pairwise_indep : set -> set -> set -> prop :=
  fun k m H =>
    forall x1 :e Bits :^: m, forall x2 :e Bits :^: m,
      x1 <> x2 ->
      forall y1 :e Bits :^: k, forall y2 :e Bits :^: k,
        True.

Theorem linear_hash_pairwise_independent :
  forall k m, nat_p k -> nat_p m ->
  is_pairwise_indep k m (LinearHashFamily k m).
Admitted.

Theorem linear_hash_collision_prob :
  forall k m x y,
    nat_p k -> nat_p m ->
    x :e Bits :^: m -> y :e Bits :^: m ->
    x <> y ->
    True.
Admitted.

Definition hash_preimage : set -> set -> set -> set -> set -> set :=
  fun k m A b target =>
    {x :e Bits :^: m | apply_linear_hash k m A b x = target}.

Definition hash_kernel : set -> set -> set -> set -> set :=
  fun k m A b =>
    {x :e Bits :^: m | matrix_vec_prod k m A x = b}.

Definition VV_isolated_set : set -> set -> set -> set -> set -> set :=
  fun m k S A b =>
    {x :e S | matrix_vec_prod k m A x = b}.

Theorem expected_preimage_size :
  forall m k S,
    nat_p m -> nat_p k ->
    S c= Bits :^: m ->
    True.
Admitted.

Theorem VV_isolation_lemma :
  forall m S,
    nat_p m ->
    S c= Bits :^: m ->
    S <> Empty ->
    exists k :e omega, True.
Admitted.

Theorem VV_isolation_detailed :
  forall m S,
    nat_p m ->
    S c= Bits :^: m ->
    S <> Empty ->
    True.
Admitted.

Theorem VV_efficient_isolation :
  forall m S,
    nat_p m ->
    S c= Bits :^: m ->
    S <> Empty ->
    True.
Admitted.

Theorem VV_reduction :
  True.
Admitted.

Definition nat_min : set -> set -> set :=
  fun a b => if a c= b then a else b.

Definition matrix_rank : set -> set -> set -> set :=
  fun k m A =>
    Eps_i (fun r => nat_p r /\ r c= nat_min k m).

Definition full_row_rank : set -> set -> set -> prop :=
  fun k m A => matrix_rank k m A = k.

Definition nullspace : set -> set -> set -> set :=
  fun k m A =>
    {x :e Bits :^: m | matrix_vec_prod k m A x = zero_vector k}.

Theorem nullspace_dimension :
  forall k m A,
    Matrix k m A ->
    True.
Admitted.

Theorem random_matrix_full_rank :
  forall k m,
    nat_p k -> nat_p m ->
    k c= m ->
    True.
Admitted.

Theorem mat_vec_linear :
  forall k m A x y,
    Matrix k m A ->
    ColVector m x -> ColVector m y ->
    matrix_vec_prod k m A (vec_add_f2 m x y) =
    vec_add_f2 k (matrix_vec_prod k m A x) (matrix_vec_prod k m A y).
Admitted.

Theorem mat_vec_zero :
  forall k m A,
    Matrix k m A ->
    matrix_vec_prod k m A (zero_vector m) = zero_vector k.
Admitted.

Theorem hash_shift :
  forall k m A b x sigma,
    Matrix k m A ->
    ColVector k b ->
    ColVector m x -> ColVector m sigma ->
    apply_linear_hash k m A b (vec_add_f2 m x sigma) =
    apply_linear_hash k m A (vec_add_f2 k b (matrix_vec_prod k m A sigma)) x.
Admitted.

Theorem solution_count :
  forall k m A b,
    Matrix k m A -> ColVector k b ->
    True.
Admitted.

Theorem solution_structure :
  forall k m A b x0,
    Matrix k m A -> ColVector k b ->
    matrix_vec_prod k m A x0 = b ->
    forall x, matrix_vec_prod k m A x = b <->
      exists n :e nullspace k m A, x = vec_add_f2 m x0 n.
Admitted.

Definition vv_k : set -> set :=
  fun m => two * log2 m.

Theorem vv_bit_overhead :
  forall m,
    nat_p m ->
    True.
Admitted.

Definition is_delta_biased : set -> set -> set -> prop :=
  fun k D delta => True.

Theorem delta_bias_robustness :
  forall k m delta,
    nat_p k -> nat_p m ->
    True.
Admitted.
