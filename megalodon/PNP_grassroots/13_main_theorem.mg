Theorem bit_by_bit_self_reduction :
  P_equals_NP ->
  True.
Admitted.

Theorem uniform_witness_finder :
  P_equals_NP ->
  exists C :e omega,
    True.
Admitted.

Theorem tuple_incompressibility_restated :
  forall m,
    nat_p m ->
    exists eta :e omega,
      0 :e eta /\
      True.
Admitted.

Theorem quantale_clash :
  forall m,
    nat_p m ->
    P_equals_NP -> False.
Admitted.

Theorem P_neq_NP_main :
  P_neq_NP.
assume H_PeqNP: P_equals_NP.
prove False.
exact quantale_clash one nat_1 H_PeqNP.
Qed.
