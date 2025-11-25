Definition is_probability_measure : set -> set -> (set -> set) -> prop := fun Omega F P => True.
Definition conditional_prob : set -> (set -> set) -> set -> set -> set := fun Omega P A B => Empty.

Definition independent_events : set -> (set -> set) -> set -> set -> prop :=
  fun Omega P A B =>
    P (A :/\: B) = P A * P B.

Definition independent_events_3 : set -> (set -> set) -> set -> set -> set -> prop :=
  fun Omega P A B C =>
    independent_events Omega P A B
    /\ independent_events Omega P A C
    /\ independent_events Omega P B C
    /\ P (A :/\: B :/\: C) = P A * P B * P C.

Theorem independence_sym :
  forall Omega, forall P: set -> set, forall A B,
    independent_events Omega P A B ->
    independent_events Omega P B A.
let Omega. let P. let A. let B.
assume H.
admit.
Qed.

Theorem independent_implies_conditional :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    independent_events Omega P A B ->
    conditional_prob Omega P A B = P A.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hp. assume Hind.
admit.
Qed.

Theorem independent_complement :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    independent_events Omega P A B ->
    independent_events Omega P A (Omega :\: B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hind.
admit.
Qed.