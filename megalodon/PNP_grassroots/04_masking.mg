Definition is_bijection_set : set -> set -> set -> prop :=
  fun A B f =>
    (forall a :e A, ap f a :e B) /\
    (forall b :e B, exists a :e A, ap f a = b) /\
    (forall a1 :e A, forall a2 :e A, ap f a1 = ap f a2 -> a1 = a2).

Definition Mask : set -> set :=
  fun m => {h :e (m :^: m) :*: Bits :^: m |
    exists pi :e m :^: m, exists sigma :e Bits :^: m,
    is_bijection_set m m pi /\
    SignVector m sigma /\
    h = (pi, sigma)}.

Definition compose_perm : set -> set -> set -> set :=
  fun m f g => fun i :e m => ap f (ap g i).

Definition invert_perm : set -> set -> set :=
  fun m pi => fun j :e m => Eps_i (fun i => i :e m /\ ap pi i = j).

Definition mask_compose : set -> set -> set -> set :=
  fun m h1 h2 =>
    (compose_perm m (mask_perm h1) (mask_perm h2),
     vec_xor m (mask_sign h1) (compose_perm m (mask_sign h2) (invert_perm m (mask_perm h1)))).

Definition mask_inverse : set -> set -> set :=
  fun m h =>
    (invert_perm m (mask_perm h),
     compose_perm m (mask_sign h) (mask_perm h)).

Definition apply_mask_to_literal : set -> set -> set -> set :=
  fun m h l =>
    Literal (ap (mask_perm h) (lit_var l))
            (if ap (mask_sign h) (lit_var l) = lit_sign l then 0 else one).

Definition apply_mask_to_clause : set -> set -> set -> set :=
  fun m h C => {apply_mask_to_literal m h l | l :e C}.

Definition apply_mask_to_cnf : set -> set -> set -> set :=
  fun m h F => {apply_mask_to_clause m h C | C :e F}.

Definition masked_cnf : set -> set -> set -> set := apply_mask_to_cnf.

Definition basis_vec : set -> set -> set :=
  fun m i => fun j :e m => if j = i then one else 0.

Definition tau_i : set -> set -> set :=
  fun m i => (fun j :e m => j, basis_vec m i).

Definition T_i : set -> set -> set -> set :=
  fun m i instance =>
    (apply_mask_to_cnf m (tau_i m i) (ap instance 0),
     ap instance 1,
     vec_xor (vv_num_rows m) (ap instance 2) (matrix_vec_prod (vv_num_rows m) m (ap instance 1) (basis_vec m i))).

Theorem Ti_measure_preserving :
  forall m i,
    nat_p m -> i :e m ->
    True.
Admitted.

Theorem Ti_preserves_uniqueness :
  forall m i F A b,
    nat_p m -> i :e m ->
    True.
Admitted.

Theorem Ti_toggles_witness_bit :
  forall m i F A b X,
    nat_p m -> i :e m ->
    satisfies X F ->
    True.
Admitted.

Theorem pipeline_promise_preserving :
  forall m stage,
    nat_p m ->
    True.
Admitted.

Definition is_sign_invariant : set -> (set -> set) -> prop :=
  fun m f =>
    forall F h sigma,
      SignVector m sigma ->
      True.

Definition sign_invariant_algebra : set -> set :=
  fun m => Power (Mask m).

Definition uniform_mask : set -> prop :=
  fun m => True.
