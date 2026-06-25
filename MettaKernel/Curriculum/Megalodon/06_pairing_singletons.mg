Theorem pair_l_in_binunion : forall x y:set, x :e {x} :\/: {y}.
let x y.
exact (binunionI1 {x} {y} x (SingI x)).
Qed.

Theorem pair_r_in_binunion : forall x y:set, y :e {x} :\/: {y}.
let x y.
exact (binunionI2 {x} {y} y (SingI y)).
Qed.

Theorem binunion_self : forall x z:set, z :e x :\/: x -> z :e x.
let x z.
assume H: z :e x :\/: x.
apply (binunionE x x z H).
- assume h: z :e x. exact h.
- assume h: z :e x. exact h.
Qed.

Theorem choice_witness : forall P:set->prop, (exists x:set, P x) -> P (Eps_i P).
let P.
assume H: exists x:set, P x.
apply H.
let x.
assume Hx: P x.
exact (Eps_i_ax P x Hx).
Qed.

Theorem succ_two_nat : nat_p (ordsucc 2).
exact (nat_ordsucc 2 nat_2).
Qed.

Theorem two_in_omega : 2 :e omega.
exact (nat_p_omega 2 nat_2).
Qed.
