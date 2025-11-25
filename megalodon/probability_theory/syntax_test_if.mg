Definition conditional_prob_test : set -> (set -> set) -> set -> set -> set :=
  fun Omega P A B =>
    If_i (0 < P B) (P (A :/\: B) :/: P B) 0.
