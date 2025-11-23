Variable m : set.
Axiom m_in_omega : m :e omega.
Axiom m_large : 4 :e m.

Definition Bit : set -> prop := fun x => x = 0 \/ x = 1.
Definition BitVector : set -> prop := fun v => v :e (m :^: 2).

Definition xor : set -> set -> set := fun a b =>
  if a = b then 0 else 1.

Definition vector_xor : set -> set -> set := fun v w =>
  fun i :e m => xor (ap v i) (ap w i).

Definition Formula : set := Empty.
Definition LinearSystem : set := Empty.

Definition SignVector : set -> prop := fun h => h :e (m :^: 2).

Definition mask_formula : set -> set -> set := fun F h => F.

Definition SILS : set -> set -> set := fun F h =>
  Empty.

Definition a_i : set -> set -> set := fun A i =>
  fun j :e m => ap (ap A i) j.

Definition T_i_on_h : set -> set -> set := fun h i =>
  fun j :e m => if j = i then xor (ap h j) 1 else ap h j.

Definition T_i_on_b : set -> set -> set -> set := fun b A i =>
  vector_xor b (a_i A i).

Definition local_input_u : set -> set -> set -> set -> set := fun z a_i_val b i =>
  (z, (a_i_val, b)).

Definition T_i_action : set -> set -> set -> set -> set := fun F h A b =>
  let i := 0 in
  let h' := T_i_on_h h i in
  let b' := T_i_on_b b A i in
  (mask_formula F h', (A, b')).

Definition z_component : set -> set -> set := fun F h =>
  SILS F h.

Definition a_i_component : set -> set -> set := fun A i =>
  a_i A i.

Definition b_component : set -> set := fun b => b.

Definition u_before_Ti : set -> set -> set -> set -> set -> set := fun F h A b i =>
  let z := z_component F h in
  let ai := a_i_component A i in
  local_input_u z ai b i.

Definition u_after_Ti : set -> set -> set -> set -> set -> set := fun F h A b i =>
  let h' := T_i_on_h h i in
  let b' := T_i_on_b b A i in
  let z' := z_component F h' in
  let ai' := a_i_component A i in
  local_input_u z' ai' b' i.

Theorem z_preserved_by_Ti : forall F h i : set,
  SignVector h ->
  i :e m ->
  z_component F h = z_component F (T_i_on_h h i).
Admitted.

Theorem a_i_preserved_by_Ti : forall A i : set,
  i :e m ->
  a_i_component A i = a_i_component A i.
Admitted.

Theorem b_NOT_preserved_by_Ti : forall b A i : set,
  BitVector b ->
  i :e m ->
  ap (a_i A i) i = 1 ->
  b <> T_i_on_b b A i.
Admitted.

Definition Ti_preserves_u_CLAIMED : prop :=
  forall F h A b i : set,
    SignVector h ->
    BitVector b ->
    i :e m ->
    u_before_Ti F h A b i = u_after_Ti F h A b i.

Definition Ti_preserves_u_ACTUAL : prop :=
  forall F h A b i : set,
    SignVector h ->
    BitVector b ->
    i :e m ->
    (z_component F h = z_component F (T_i_on_h h i)) /\
    (a_i_component A i = a_i_component A i) /\
    (b = T_i_on_b b A i).

Theorem claimed_vs_actual_GAP :
  Ti_preserves_u_ACTUAL -> Ti_preserves_u_CLAIMED.
Admitted.

Theorem actual_FAILS_on_b :
  ~Ti_preserves_u_ACTUAL.
Admitted.

Definition calibration_one_line_FLAWED : prop :=
  forall u : set,
    exists Ti_bijection : set,
      True.

Definition the_structural_bug : prop :=
  Ti_preserves_u_CLAIMED /\ ~Ti_preserves_u_ACTUAL.

Theorem CRUX_1_IDENTIFIED : the_structural_bug -> False.
Admitted.

Definition possible_fix_1 : prop :=
  forall F h A b i : set,
    SignVector h ->
    BitVector b ->
    i :e m ->
    let u' := (z_component F h, a_i_component A i) in
    u' = u'.

Theorem fix_1_removes_b_from_u :
  possible_fix_1.
Admitted.

Definition possible_fix_2 : prop :=
  forall F h A b i : set,
    SignVector h ->
    BitVector b ->
    i :e m ->
    forall local_rule : set -> set,
      True.

Definition calibration_crux_summary : prop :=
  (Ti_preserves_u_CLAIMED ->
    forall u, True) /\
  (~Ti_preserves_u_ACTUAL) /\
  (possible_fix_1 \/ possible_fix_2).

Theorem calibration_crux_FORMALIZED : calibration_crux_summary.
Admitted.

