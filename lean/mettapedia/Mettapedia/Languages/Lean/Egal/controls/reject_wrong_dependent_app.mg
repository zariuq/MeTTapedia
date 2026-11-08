
(** Rejection control: the type of a dependent application is the family at
    the argument given, not at another index. **)

Theorem wrong_dependent_app : forall f :e (Pi_ n :e omega, ordsucc n), f 1 :e ordsucc 0.
let f. assume Hf: f :e (Pi_ n :e omega, ordsucc n).
exact ap_Pi omega ordsucc f 1 Hf (nat_p_omega 1 nat_1).
Qed.
