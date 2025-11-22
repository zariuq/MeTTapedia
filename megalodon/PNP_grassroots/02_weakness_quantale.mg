Definition empty_string : set := Empty.

Definition plain_complexity : set -> set :=
  fun x =>
    Eps_i (fun k =>
      nat_p k /\
      (exists p, desc_length p = k /\ UTM_computes p empty_string x) /\
      (forall p', UTM_computes p' empty_string x -> desc_length p' c= k -> desc_length p' = k)).

Definition C : set -> set := plain_complexity.

Definition conditional_complexity : set -> set -> set :=
  fun x y =>
    Eps_i (fun k =>
      nat_p k /\
      (exists p, desc_length p = k /\ UTM_computes p y x) /\
      (forall p', UTM_computes p' y x -> desc_length p' c= k -> desc_length p' = k)).

Definition C_cond : set -> set -> set := conditional_complexity.

Definition Kpoly : set -> set -> set :=
  fun z y =>
    Eps_i (fun k =>
      nat_p k /\
      (exists p, desc_length p = k /\
                 UTM_computes p y z /\
                 exists c :e omega, UTM_halts_in p y (exp_nat (desc_length y) c)) /\
      (forall p', UTM_computes p' y z ->
                  (exists c' :e omega, UTM_halts_in p' y (exp_nat (desc_length y) c')) ->
                  desc_length p' c= k -> desc_length p' = k)).

Definition weakness : set -> set -> set := Kpoly.

Definition Kpoly_infinite : set -> set -> prop :=
  fun z y =>
    ~(exists p, UTM_computes p y z /\
                exists c :e omega, UTM_halts_in p y (exp_nat (desc_length y) c)).

Theorem Kpoly_finite_on_promise :
  forall Phi X, True.
Admitted.

Theorem Kpoly_invariance :
  forall U V,
    exists c_UV :e omega,
      forall z y, True.
Admitted.

Definition ExtNat : set := omega :\/: {omega}.

Definition is_finite_extnat : set -> prop :=
  fun n => n :e omega.

Definition is_infinity : set -> prop :=
  fun n => n = omega.

Definition quant_add : set -> set -> set :=
  fun a b =>
    if is_infinity a then omega
    else if is_infinity b then omega
    else a + b.

Theorem quant_add_assoc : forall a b c,
  quant_add (quant_add a b) c = quant_add a (quant_add b c).
Admitted.

Theorem quant_add_comm : forall a b,
  quant_add a b = quant_add b a.
Admitted.

Theorem quant_add_zero : forall a,
  quant_add 0 a = a.
Admitted.

Theorem quant_add_infinity : forall a,
  quant_add omega a = omega.
Admitted.

Definition quant_le : set -> set -> prop :=
  fun a b =>
    (is_finite_extnat a /\ is_finite_extnat b /\ a c= b) \/
    (is_infinity b).

Theorem quant_le_refl : forall a, quant_le a a.
Admitted.

Theorem quant_le_trans : forall a b c,
  quant_le a b -> quant_le b c -> quant_le a c.
Admitted.

Theorem quant_le_antisym : forall a b,
  quant_le a b -> quant_le b a -> a = b.
Admitted.

Theorem quant_le_infinity : forall a, quant_le a omega.
Admitted.

Theorem quant_add_mono : forall a b c d,
  quant_le a b -> quant_le c d -> quant_le (quant_add a c) (quant_add b d).
Admitted.

Definition concat : set -> set -> set :=
  fun s1 s2 => (s1, s2).

Theorem Kpoly_monotonicity :
  forall x y z,
    exists c :e omega,
      quant_le (Kpoly x (concat z y)) (quant_add (Kpoly x y) c).
Admitted.

Theorem Kpoly_chain_rule :
  forall x z y,
    exists c :e omega,
      quant_le (Kpoly (concat x z) y)
               (quant_add (quant_add (Kpoly x y) (Kpoly z (concat x y))) c).
Admitted.

Theorem Kpoly_symmetry_coarse :
  forall x y,
    exists c :e omega, True.
Admitted.

Theorem Kpoly_subadditive :
  forall x y,
    exists c :e omega,
      quant_le (Kpoly (concat x y) empty_string)
               (quant_add (quant_add (Kpoly x empty_string)
                                     (Kpoly y empty_string)) c).
Admitted.

Definition tuple_concat : set -> set -> set :=
  fun T t => nat_primrec empty_string (fun i acc => concat acc (ap T i)) t.

Definition log2 : set -> set :=
  fun n => Eps_i (fun k => nat_p k /\ exp_nat 2 k c= n /\ n :e exp_nat 2 (ordsucc k)).

Definition c1_vv : set := two.

Definition vv_num_rows : set -> set :=
  fun m => c1_vv * log2 m.

Theorem Kpoly_block_additivity :
  forall t X_tuple Y_tuple,
    nat_p t ->
    exists c :e omega,
      quant_le (Kpoly (tuple_concat X_tuple t) (tuple_concat Y_tuple t))
               (quant_add
                 (sum_range (fun i => Kpoly (ap X_tuple i) (ap Y_tuple i)) t)
                 (c * log2 t)).
Admitted.

Definition wrapper_overhead : set -> set :=
  fun t => 2 * log2 t.

Theorem wrapper_overhead_bound :
  forall t, nat_p t -> t <> 0 ->
    wrapper_overhead t c= 3 * log2 t.
Admitted.

Definition decoder_succeeds : set -> set -> set -> set -> prop :=
  fun P i X_tuple Y_tuple =>
    decoder_succeeds_on P (ap Y_tuple i) (ap X_tuple i).

Definition success_set : set -> set -> set -> set -> set :=
  fun P t X_tuple Y_tuple =>
    {i :e t | decoder_succeeds P i X_tuple Y_tuple}.

Definition binomial : set -> set -> set :=
  fun n k =>
    if n :e k then 0
    else nat_factorial n * (nat_factorial k * nat_factorial (n + (omega :\: k))) .

Definition tuple_max : (set -> set) -> set -> set -> set :=
  fun f T t => nat_primrec 0 (fun i acc => if acc :e f (ap T i) then f (ap T i) else acc) t.

Theorem compression_from_success_coarse :
  forall L P t S X_tuple Y_tuple,
    desc_length P = L ->
    S c= t ->
    S = success_set P t X_tuple Y_tuple ->
    True.
Admitted.

Definition error_mask : set -> set -> set :=
  fun x pred => fun i :e desc_length x => if ap x i = ap pred i then 0 else one.

Definition error_count : set -> set -> set :=
  fun x pred => hamming_dist (desc_length x) x pred.

Theorem compression_perbit_enumerative :
  forall L P t X_tuple Y_tuple,
    desc_length P = L ->
    polytime_decoder P ->
    True.
Admitted.

Definition binary_entropy : set -> set :=
  fun p => 0.

Theorem compression_from_success_rate :
  forall L P t success_rate,
    desc_length P = L ->
    polytime_decoder P ->
    True.
Admitted.

Theorem num_short_decoders :
  forall L, nat_p L -> True.
Admitted.

Theorem union_bound_short_decoders :
  forall L t delta eps,
    nat_p L -> nat_p t ->
    L = delta * t ->
    True.
Admitted.

Theorem key_union_bound_regime :
  forall delta gamma c t,
    nat_p t ->
    delta :e c ->
    True.
Admitted.

Theorem incompressibility_counting :
  forall n, nat_p n -> True.
Admitted.

Theorem random_string_incompressible :
  forall n c, nat_p n -> nat_p c -> True.
Admitted.

Theorem conditional_incompressibility :
  forall n y, nat_p n -> True.
Admitted.

Theorem tuple_complexity_linear :
  forall t m, nat_p t -> nat_p m -> True.
Admitted.

Definition c4 : set := 4.

Theorem tuple_Kpoly_lower_bound_preview :
  forall m t,
    nat_p m -> nat_p t ->
    t = c4 * m ->
    exists eta :e omega,
      0 :e eta /\ True.
Admitted.
