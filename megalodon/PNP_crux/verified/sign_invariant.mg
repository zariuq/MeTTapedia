Definition Bit : set -> prop := fun b => b :e 2.
Definition xor : set -> set -> set := fun a b => if a = b then 0 else 1.

Theorem xor_0_0 : xor 0 0 = 0.
exact If_i_1 (0 = 0) 0 1 (fun Q H => H).
Qed.

Theorem xor_1_1 : xor 1 1 = 0.
exact If_i_1 (1 = 1) 0 1 (fun Q H => H).
Qed.

Theorem xor_0_1 : xor 0 1 = 1.
exact If_i_0 (0 = 1) 0 1 neq_0_1.
Qed.

Theorem xor_1_0 : xor 1 0 = 1.
exact If_i_0 (1 = 0) 0 1 neq_1_0.
Qed.

Theorem bit_cases : forall b, Bit b -> b = 0 \/ b = 1.
let b.
assume Hb: Bit b.
exact cases_2 b Hb (fun i => i = 0 \/ i = 1) (orIL (0 = 0) (0 = 1) (fun Q H => H)) (orIR (1 = 0) (1 = 1) (fun Q H => H)).
Qed.

Theorem xor_self : forall a, Bit a -> xor a a = 0.
let a.
assume Ha: Bit a.
apply orE (a = 0) (a = 1) (xor a a = 0).
assume Ha0: a = 0.
rewrite Ha0.
exact xor_0_0.
assume Ha1: a = 1.
rewrite Ha1.
exact xor_1_1.
exact bit_cases a Ha.
Qed.

Theorem xor_double_cancel : forall a b, Bit a -> Bit b -> xor (xor a b) b = a.
let a b.
assume Ha: Bit a.
assume Hb: Bit b.
apply orE (a = 0) (a = 1) (xor (xor a b) b = a).
assume Ha0: a = 0.
rewrite Ha0.
apply orE (b = 0) (b = 1) (xor (xor 0 b) b = 0).
assume Hb0: b = 0.
rewrite Hb0.
rewrite xor_0_0.
exact xor_0_0.
assume Hb1: b = 1.
rewrite Hb1.
rewrite xor_0_1.
exact xor_1_1.
exact bit_cases b Hb.
assume Ha1: a = 1.
rewrite Ha1.
apply orE (b = 0) (b = 1) (xor (xor 1 b) b = 1).
assume Hb0: b = 0.
rewrite Hb0.
rewrite xor_1_0.
exact xor_1_0.
assume Hb1: b = 1.
rewrite Hb1.
rewrite xor_1_1.
exact xor_0_1.
exact bit_cases b Hb.
exact bit_cases a Ha.
Qed.

Variable m : set.
Axiom m_in_omega : m :e omega.

Definition neg_bit : set -> set := fun a => xor a 1.

Theorem neg_bit_0 : neg_bit 0 = 1.
exact xor_0_1.
Qed.

Theorem neg_bit_1 : neg_bit 1 = 0.
exact xor_1_1.
Qed.

Theorem neg_bit_involution : forall a, Bit a -> neg_bit (neg_bit a) = a.
let a.
assume Ha: Bit a.
apply orE (a = 0) (a = 1) (neg_bit (neg_bit a) = a).
assume Ha0: a = 0.
rewrite Ha0.
rewrite neg_bit_0.
exact neg_bit_1.
assume Ha1: a = 1.
rewrite Ha1.
rewrite neg_bit_1.
exact neg_bit_0.
exact bit_cases a Ha.
Qed.

Theorem neg_bit_different : forall a, Bit a -> a <> neg_bit a.
let a.
assume Ha: Bit a.
apply orE (a = 0) (a = 1) (a <> neg_bit a).
assume Ha0: a = 0.
rewrite Ha0.
rewrite neg_bit_0.
exact neq_0_1.
assume Ha1: a = 1.
rewrite Ha1.
rewrite neg_bit_1.
exact neq_1_0.
exact bit_cases a Ha.
Qed.

Definition BitVec : set -> prop := fun v => v :e (m :^: 2).

Definition xor_vec : set -> set -> set := fun v1 v2 =>
  fun i :e m => xor (ap v1 i) (ap v2 i).

Definition flip_vec_at : set -> set -> set := fun i v =>
  fun j :e m => if j = i then neg_bit (ap v j) else ap v j.

Definition SignInvariant : (set -> prop) -> prop := fun P =>
  forall v sigma, P v -> BitVec sigma -> P v.

