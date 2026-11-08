(** Multiplication: the product of LeanNum m and LeanNum n is LeanNum of
    mul_nat m n.  Egal's
    mul_nat adds on the left and Lean's Nat.mul on the right, so the step
    uses commutativity of add_nat. **)
Theorem LeanNum_mul : forall m, nat_p m -> forall n, nat_p n ->
  Lean_Nat_mul (LeanNum m) (LeanNum n) = LeanNum (mul_nat m n).
let m. assume Hm: nat_p m.
apply nat_ind.
- prove Lean_Nat_mul (LeanNum m) (LeanNum 0) = LeanNum (mul_nat m 0).
  rewrite mul_nat_0R m.
  exact Lean_Nat_mul_eq_1 (LeanNum m) (LeanNum_In m Hm).
- let n. assume Hn: nat_p n.
  assume IH: Lean_Nat_mul (LeanNum m) (LeanNum n) = LeanNum (mul_nat m n).
  prove Lean_Nat_mul (LeanNum m) (LeanNum (ordsucc n)) = LeanNum (mul_nat m (ordsucc n)).
  rewrite mul_nat_SR m n Hn.
  rewrite add_nat_com m Hm (mul_nat m n) (mul_nat_p m Hm n Hn).
  rewrite LeanNum_S n Hn.
  rewrite Lean_Nat_mul_eq_2 (LeanNum m) (LeanNum_In m Hm) (LeanNum n) (LeanNum_In n Hn).
  rewrite IH.
  exact LeanNum_add (mul_nat m n) (mul_nat_p m Hm n Hn) m Hm.
Qed.

Theorem LeanNum_mul_eq : forall m, nat_p m -> forall n, nat_p n -> forall k,
  mul_nat m n = k -> Lean_Nat_mul (LeanNum m) (LeanNum n) = LeanNum k.
let m. assume Hm: nat_p m. let n. assume Hn: nat_p n. let k. assume Hk: mul_nat m n = k.
rewrite <- Hk.
exact LeanNum_mul m Hm n Hn.
Qed.
