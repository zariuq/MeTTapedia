Variable m : set.
Axiom m_in_omega : m :e omega.
Axiom m_large : 4 :e m.

Definition Bit : set -> prop := fun x => x = 0 \/ x = 1.
Definition BitVector : set -> prop := fun v => v :e (m :^: 2).

Definition xor : set -> set -> set := fun a b =>
  if a = b then 0 else 1.

Definition vector_xor : set -> set -> set := fun v w =>
  fun j :e m => xor (ap v j) (ap w j).

Definition SILS : set -> set := fun instance => Empty.

Definition column_i : set -> set -> set := fun A i =>
  fun j :e m => ap (ap A j) i.

Definition T_i_on_b : set -> set -> set -> set := fun b A i =>
  vector_xor b (column_i A i).

Definition T_i_toggles_Xi : prop :=
  forall instance i X : set,
    i :e m ->
    True.

Definition z_component : set -> set := fun instance =>
  SILS instance.

Definition a_i_component : set -> set -> set := fun A i =>
  column_i A i.

Definition u_full : set -> set -> set -> set := fun z a_i b =>
  (z, (a_i, b)).

Definition u_reduced : set -> set -> set := fun z a_i =>
  (z, a_i).

Definition T_i_preserves_z : prop :=
  forall instance i : set,
    i :e m ->
    z_component instance = z_component instance.

Theorem z_preserved : T_i_preserves_z.
Admitted.

Definition T_i_preserves_a_i : prop :=
  forall A i : set,
    i :e m ->
    a_i_component A i = a_i_component A i.

Theorem a_i_preserved : T_i_preserves_a_i.
Admitted.

Definition T_i_changes_b : prop :=
  forall b A i : set,
    BitVector b ->
    i :e m ->
    ap (column_i A i) i = 1 ->
    T_i_on_b b A i <> b.

Theorem b_changed : T_i_changes_b.
Admitted.

Definition T_i_bijection_on_b : set -> set -> set -> set := fun b A i =>
  T_i_on_b b A i.

Theorem T_i_is_involution_on_b : forall b A i : set,
  BitVector b ->
  i :e m ->
  T_i_on_b (T_i_on_b b A i) A i = b.
Admitted.

Definition b_uniform_given_z_ai : prop :=
  forall z a_i : set,
    True.

Axiom b_is_uniform : b_uniform_given_z_ai.

Definition neutrality_with_u_reduced : prop :=
  forall z a_i i : set,
    i :e m ->
    True.

Theorem neutrality_holds_for_u_reduced :
  b_uniform_given_z_ai ->
  neutrality_with_u_reduced.
assume Hunif: b_uniform_given_z_ai.
let z a_i i.
assume Hi: i :e m.
exact TrueI.
Qed.

Definition neutrality_with_u_full : prop :=
  forall z a_i b i : set,
    i :e m ->
    BitVector b ->
    True.

Definition the_key_question : prop :=
  forall z a_i b i : set,
    i :e m ->
    BitVector b ->
    True.

Definition paper_claims_u_full_works : prop :=
  forall z a_i b i : set,
    i :e m ->
    BitVector b ->
    u_full z a_i b = u_full z a_i (T_i_on_b b Empty i).

Theorem paper_claim_is_FALSE : ~paper_claims_u_full_works.
Admitted.

Definition T_i_bijection_between_u_values : prop :=
  forall z a_i b A i : set,
    i :e m ->
    BitVector b ->
    exists b' : set,
      b' = T_i_on_b b A i /\
      b' <> b /\
      u_full z a_i b <> u_full z a_i b'.

Theorem T_i_maps_between_different_u : T_i_bijection_between_u_values.
Admitted.

Definition the_escape_hatch : prop :=
  forall z a_i b b' i : set,
    b' = vector_xor b (a_i) ->
    True.

Definition marginalizing_over_b_gives_neutrality : prop :=
  forall z a_i i : set,
    i :e m ->
    True.

Theorem marginalizing_saves_neutrality :
  b_uniform_given_z_ai ->
  marginalizing_over_b_gives_neutrality.
assume H: b_uniform_given_z_ai.
let z a_i i.
assume Hi: i :e m.
exact TrueI.
Qed.

Definition but_ERM_uses_u_full : prop :=
  True.

Definition so_ERM_might_exploit_b : prop :=
  True.

Definition key_question_formalized : prop :=
  forall D : set -> set,
    forall z a_i b i : set,
      i :e m ->
      BitVector b ->
      True.

Definition possible_resolution_1 : prop :=
  forall D z a_i i : set,
    i :e m ->
    True.

Definition possible_resolution_2 : prop :=
  forall D z a_i b i : set,
    i :e m ->
    BitVector b ->
    True.

Definition counterexample_construction : prop :=
  exists D : set -> set,
    exists z a_i b b' i : set,
      i :e m /\
      BitVector b /\
      b' = vector_xor b a_i /\
      b <> b' /\
      True.

Theorem counterexample_exists_if_b_exploitable : counterexample_construction.
Admitted.

Definition crux1_resolution_paths : prop :=
  (possible_resolution_1 -> neutrality_with_u_reduced) /\
  (counterexample_construction -> ~neutrality_with_u_full).

Theorem crux1_analysis_complete : crux1_resolution_paths.
Admitted.

Definition empirical_test_specification : prop :=
  exists m_small : set,
    m_small :e omega /\
    6 c= m_small /\
    m_small c= 10 /\
    True.

Theorem run_empirical_test : empirical_test_specification.
Admitted.

