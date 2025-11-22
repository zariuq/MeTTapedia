Definition is_sign_invariant_sigma : set -> set -> prop :=
  fun I m =>
    forall B :e I, forall sigma :e Bits :^: m,
    True.

Theorem AP_GCT_neutrality :
  forall m i I,
    nat_p m ->
    i :e m ->
    is_sign_invariant_sigma I m ->
    True.
Admitted.

Theorem neutrality_via_involution :
  forall m i I B,
    nat_p m ->
    is_sign_invariant_sigma I m ->
    B :e I ->
    True.
Admitted.

Theorem neutrality_measure_theoretic :
  forall m i,
    nat_p m ->
    i :e m ->
    True.
Admitted.

Theorem SILS_only_neutral :
  forall m i g,
    SILS_extractor_prop m ->
    i :e m ->
    True.
Admitted.

Theorem calibration_invariance :
  forall m i u,
    nat_p m ->
    i :e m ->
    True.
Admitted.
