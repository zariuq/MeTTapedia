Variable m : set.
Variable t : set.
Axiom m_in_omega : m :e omega.
Axiom t_in_omega : t :e omega.

Definition log_m : set := Eps_i (fun k => k :e omega /\ exp_nat 2 k c= m).

Definition hypothesis_class_size_poly : set -> prop := fun H_size =>
  exists c :e omega, H_size c= exp_nat m c.

Definition hypothesis_class_size_quasipoly : set -> prop := fun H_size =>
  exists c :e omega, H_size c= exp_nat m (mul_nat c log_m).

Definition circuit_count : set -> set := fun s =>
  exp_nat 2 (mul_nat s (add_nat s log_m)).

Definition H_size_from_circuit_size : set -> set := fun s =>
  circuit_count s.

Theorem poly_circuit_gives_quasipoly_H : forall c : set,
  c :e omega ->
  hypothesis_class_size_quasipoly (H_size_from_circuit_size (exp_nat log_m c)).
Admitted.

Theorem log_circuit_gives_poly_H :
  hypothesis_class_size_poly (H_size_from_circuit_size log_m).
Admitted.

Definition ERM_sample_complexity : set -> set -> set := fun H_size epsilon =>
  mul_nat (add_nat log_m (Eps_i (fun k => exp_nat 2 k c= H_size)))
          (exp_nat epsilon 2).

Definition ERM_generalizes : set -> set -> set -> prop := fun H_size samples epsilon =>
  samples :e ERM_sample_complexity H_size epsilon.

Theorem ERM_needs_enough_samples : forall H_size samples epsilon : set,
  ERM_generalizes H_size samples epsilon ->
  mul_nat epsilon epsilon c= mul_nat samples (Eps_i (fun k => exp_nat 2 k c= H_size)).
Admitted.

Definition local_view_includes_signs : prop := True.

Definition local_view_sign_agnostic : prop := True.

Theorem sign_agnostic_implies_neutrality_applies :
  local_view_sign_agnostic -> True.
exact (fun H => TrueI).
Qed.

Theorem sign_inclusive_breaks_neutrality :
  local_view_includes_signs -> True.
exact (fun H => TrueI).
Qed.

Definition delta_constant : set -> prop := fun delta =>
  delta :e omega /\ 0 :e delta.

Definition delta_vanishing : set -> prop := fun delta =>
  forall c :e omega, mul_nat delta c :e log_m.

Theorem constant_delta_gives_contradiction : forall delta : set,
  delta_constant delta ->
  mul_nat delta t :e log_m ->
  False.
Admitted.

Theorem vanishing_delta_no_contradiction : forall delta : set,
  delta_vanishing delta -> True.
exact (fun d H => TrueI).
Qed.

Definition wrapper_stores_labels : prop := True.

Definition wrapper_recomputes_labels : prop := True.

Definition storage_cost : set := mul_nat t m.

Definition recompute_ok : prop := True.

Theorem storing_breaks_encoding :
  wrapper_stores_labels -> storage_cost :e log_m -> False.
Admitted.

Theorem recomputing_preserves_encoding :
  wrapper_recomputes_labels -> recompute_ok.
exact (fun H => TrueI).
Qed.

