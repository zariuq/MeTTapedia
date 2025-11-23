Definition even : set -> prop := fun n => exists k:set, nat_p k /\ n = mul_nat 2 k.

Definition odd : set -> prop := fun n => exists k:set, nat_p k /\ n = add_nat (mul_nat 2 k) 1.

Theorem nat_p_2 : nat_p 2.
exact nat_2.
Qed.

Theorem set_eq_refl : forall x:set, x = x.
let x.
prove forall Q: set -> set -> prop, Q x x -> Q x x.
let Q. assume HQ: Q x x. exact HQ.
Qed.

Theorem even_0 : even 0.
prove exists k:set, nat_p k /\ 0 = mul_nat 2 k.
witness 0.
apply andI (nat_p 0) (0 = mul_nat 2 0).
- exact nat_0.
- prove 0 = mul_nat 2 0.
  claim H: mul_nat 2 0 = 0. exact mul_nat_0R 2.
  prove forall Q: set -> set -> prop, Q 0 (mul_nat 2 0) -> Q (mul_nat 2 0) 0.
  let Q. assume HQ: Q 0 (mul_nat 2 0).
  exact H (fun a b => Q b a) HQ.
Qed.

Theorem odd_1 : odd 1.
prove exists k:set, nat_p k /\ 1 = add_nat (mul_nat 2 k) 1.
witness 0.
apply andI (nat_p 0) (1 = add_nat (mul_nat 2 0) 1).
- exact nat_0.
- prove 1 = add_nat (mul_nat 2 0) 1.
  claim H1: mul_nat 2 0 = 0. exact mul_nat_0R 2.
  claim H2: add_nat 0 1 = 1. exact add_nat_0L 1 nat_1.
  claim H3: add_nat (mul_nat 2 0) 1 = add_nat 0 1.
    prove forall Q: set -> set -> prop, Q (add_nat (mul_nat 2 0) 1) (add_nat 0 1) -> Q (add_nat 0 1) (add_nat (mul_nat 2 0) 1).
    let Q. assume HQ: Q (add_nat (mul_nat 2 0) 1) (add_nat 0 1).
    exact H1 (fun a b => Q (add_nat a 1) (add_nat b 1)) HQ.
  claim H4: add_nat (mul_nat 2 0) 1 = 1.
    exact eq_i_tra (add_nat (mul_nat 2 0) 1) (add_nat 0 1) 1 H3 H2.
  prove forall Q: set -> set -> prop, Q 1 (add_nat (mul_nat 2 0) 1) -> Q (add_nat (mul_nat 2 0) 1) 1.
  let Q. assume HQ: Q 1 (add_nat (mul_nat 2 0) 1).
  exact H4 (fun a b => Q b a) HQ.
Qed.

Theorem even_2 : even 2.
prove exists k:set, nat_p k /\ 2 = mul_nat 2 k.
witness 1.
apply andI (nat_p 1) (2 = mul_nat 2 1).
- exact nat_1.
- prove 2 = mul_nat 2 1.
  claim H1: mul_nat 2 1 = add_nat 2 (mul_nat 2 0). exact mul_nat_SR 2 0 nat_0.
  claim H2: mul_nat 2 0 = 0. exact mul_nat_0R 2.
  claim H3: add_nat 2 (mul_nat 2 0) = add_nat 2 0.
    prove forall Q: set -> set -> prop, Q (add_nat 2 (mul_nat 2 0)) (add_nat 2 0) -> Q (add_nat 2 0) (add_nat 2 (mul_nat 2 0)).
    let Q. assume HQ: Q (add_nat 2 (mul_nat 2 0)) (add_nat 2 0).
    exact H2 (fun a b => Q (add_nat 2 a) (add_nat 2 b)) HQ.
  claim H4: add_nat 2 0 = 2. exact add_nat_0R 2.
  claim H5: mul_nat 2 1 = add_nat 2 0.
    exact eq_i_tra (mul_nat 2 1) (add_nat 2 (mul_nat 2 0)) (add_nat 2 0) H1 H3.
  claim H6: mul_nat 2 1 = 2.
    exact eq_i_tra (mul_nat 2 1) (add_nat 2 0) 2 H5 H4.
  prove forall Q: set -> set -> prop, Q 2 (mul_nat 2 1) -> Q (mul_nat 2 1) 2.
  let Q. assume HQ: Q 2 (mul_nat 2 1).
  exact H6 (fun a b => Q b a) HQ.
Qed.

