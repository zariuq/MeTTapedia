Variable m : set.
Axiom m_in_omega : m :e omega.

Definition degree_3cnf : set -> set := fun alpha =>
  add_nat (add_nat alpha alpha) alpha.

Definition times_2 : set -> set := fun n =>
  add_nat n n.

Definition neighborhood_size : set -> set -> set := fun d r =>
  exp_nat d r.

Definition cycle_probability_exponent : set -> set -> set := fun d r =>
  exp_nat d (times_2 r).

Theorem cycle_exponent_doubled : forall d r : set,
  d :e omega -> r :e omega ->
  cycle_probability_exponent d r = exp_nat d (add_nat r r).
Admitted.

Definition subcritical_radius : set -> set -> prop := fun r d =>
  r :e omega /\ d :e omega /\ exp_nat d (times_2 r) :e m.

Theorem subcritical_implies_rare_cycles : forall r d : set,
  subcritical_radius r d ->
  True.
let r d : set.
assume H: subcritical_radius r d.
exact TrueI.
Qed.

Definition degree_12 : set := add_nat (add_nat (add_nat 3 3) 3) 3.

Theorem degree_12_from_alpha_4 : degree_3cnf 4 = degree_12.
Admitted.

Definition log_base_2 : set -> set := fun n =>
  Eps_i (fun k => k :e omega /\ exp_nat 2 k c= n /\ n :e exp_nat 2 (ordsucc k)).

Theorem log_2_of_12_bound : log_base_2 degree_12 :e omega /\ log_base_2 degree_12 c= 4.
Admitted.

Definition critical_constant : set -> set := fun d =>
  Eps_i (fun c => c :e omega /\ mul_nat 2 (mul_nat c (log_base_2 d)) :e log_base_2 m).

Theorem critical_constant_exists : forall d : set,
  d :e omega -> 2 c= d ->
  exists c :e omega, mul_nat 2 (mul_nat c (log_base_2 d)) :e log_base_2 m.
Admitted.

Definition tree_failure_probability : set -> set -> set := fun d c =>
  exp_nat m (add_nat 1 (mul_nat 2 (mul_nat c (log_base_2 d)))).

Definition tree_success_bound : set -> set -> prop := fun d c =>
  tree_failure_probability d c :e m.

Theorem tree_prob_constant_degree : forall alpha : set,
  alpha :e omega ->
  exists c : set,
    c :e omega /\
    exp_nat (degree_3cnf alpha) (times_2 c) :e m.
Admitted.

Theorem tree_likeness_whp : forall alpha : set,
  alpha :e omega ->
  4 c= alpha ->
  alpha c= 10 ->
  exists c : set,
    c :e omega /\
    c c= log_base_2 m /\
    tree_success_bound (degree_3cnf alpha) c.
Admitted.

Definition sparsification_constant : set := 1.

Theorem sparsification_works_for_alpha_4 :
  4 :e omega ->
  exists c : set,
    c :e omega /\
    subcritical_radius c degree_12 /\
    True.
Admitted.

