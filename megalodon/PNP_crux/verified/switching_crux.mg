Variable m : set.
Variable t : set.
Axiom m_in_omega : m :e omega.
Axiom t_in_omega : t :e omega.
Axiom t_large : m c= t.

Definition log_m : set := Eps_i (fun k => k :e omega /\ exp_nat 2 k c= m).

Definition Decoder : (set -> set) -> prop := fun D =>
  forall inst : set, D inst :e 2.

Definition K_poly_le : (set -> set) -> set -> prop := fun D k =>
  k :e omega.

Definition neighborhood : set -> set -> set -> set := fun G v r =>
  {u :e m | True}.

Definition Graph : set -> prop := fun G =>
  G c= m :*: m.

Definition local_view : set -> set -> set -> set := fun phi i r =>
  neighborhood phi i r.

Definition depends_only_on : (set -> set) -> set -> set -> prop := fun D i r =>
  forall phi1 phi2 : set,
    local_view phi1 i r = local_view phi2 i r ->
    D phi1 = D phi2.

Definition per_bit_local : (set -> set) -> set -> prop := fun D r =>
  forall i :e m, depends_only_on D i r.

Definition symmetrization_family : set -> set := fun seed =>
  m.

Definition apply_symmetrization : set -> set -> set := fun T phi =>
  phi.

Definition surrogate_label : (set -> set) -> set -> set -> set := fun D phi i =>
  D phi.

Definition ERM_output : set -> (set -> set) -> set -> set := fun H train i =>
  0.

Definition hypothesis_space : set -> set := fun r =>
  exp_nat 2 (exp_nat 2 r).

Definition Wrapper : (set -> set) -> set -> (set -> set) := fun D r phi =>
  ERM_output (hypothesis_space r) D phi.

Definition wrapper_is_local : (set -> set) -> set -> prop := fun D r =>
  per_bit_local (Wrapper D r) r.

Theorem wrapper_encoding_cost : forall D : set -> set, forall k : set,
  K_poly_le D k ->
  K_poly_le (Wrapper D log_m) (add_nat k log_m).
Admitted.

Definition gamma_fraction : (set -> set) -> set -> set := fun D r =>
  m.

Definition switching_success : (set -> set) -> set -> set -> prop := fun D r gamma =>
  gamma :e omega /\ 0 :e gamma /\ gamma c= t /\
  True.

Theorem switching_by_weakness_main : forall D : set -> set, forall k : set,
  Decoder D ->
  K_poly_le D k ->
  k c= log_m ->
  exists r gamma : set,
    r :e omega /\
    r c= mul_nat log_m log_m /\
    switching_success D r gamma /\
    wrapper_is_local D r.
Admitted.

Definition calibration_holds : (set -> set) -> set -> prop := fun D r =>
  forall i :e m, True.

Theorem calibration_implies_switching : forall D : set -> set, forall r : set,
  Decoder D ->
  calibration_holds D r ->
  wrapper_is_local D r.
Admitted.

Definition sign_invariant_predicate : (set -> prop) -> prop := fun P =>
  True.

Definition local_decoder_success_rate : (set -> set) -> set -> set := fun D r =>
  0.

Theorem local_plus_neutrality_gives_half : forall D : set -> set, forall r : set,
  Decoder D ->
  per_bit_local D r ->
  sign_invariant_predicate (fun phi => True) ->
  local_decoder_success_rate D r c= 1.
Admitted.

Definition delta : set := 1.

Definition lower_bound_K_poly : set := mul_nat delta t.

Definition upper_bound_K_poly : set := add_nat log_m log_m.

Theorem final_contradiction :
  t c= mul_nat m m ->
  lower_bound_K_poly :e upper_bound_K_poly ->
  False.
Admitted.

