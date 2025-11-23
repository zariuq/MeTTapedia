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

Theorem xor_is_bit : forall a b, Bit a -> Bit b -> Bit (xor a b).
let a b.
assume Ha: Bit a.
assume Hb: Bit b.
apply orE (a = 0) (a = 1) (Bit (xor a b)).
assume Ha0: a = 0.
rewrite Ha0.
apply orE (b = 0) (b = 1) (Bit (xor 0 b)).
assume Hb0: b = 0.
rewrite Hb0.
rewrite xor_0_0.
exact In_0_2.
assume Hb1: b = 1.
rewrite Hb1.
rewrite xor_0_1.
exact In_1_2.
exact bit_cases b Hb.
assume Ha1: a = 1.
rewrite Ha1.
apply orE (b = 0) (b = 1) (Bit (xor 1 b)).
assume Hb0: b = 0.
rewrite Hb0.
rewrite xor_1_0.
exact In_1_2.
assume Hb1: b = 1.
rewrite Hb1.
rewrite xor_1_1.
exact In_0_2.
exact bit_cases b Hb.
exact bit_cases a Ha.
Qed.

Theorem xor_0_l : forall b, Bit b -> xor 0 b = b.
let b.
assume Hb: Bit b.
apply orE (b = 0) (b = 1) (xor 0 b = b).
assume Hb0: b = 0.
rewrite Hb0.
exact xor_0_0.
assume Hb1: b = 1.
rewrite Hb1.
exact xor_0_1.
exact bit_cases b Hb.
Qed.

Theorem xor_0_r : forall a, Bit a -> xor a 0 = a.
let a.
assume Ha: Bit a.
apply orE (a = 0) (a = 1) (xor a 0 = a).
assume Ha0: a = 0.
rewrite Ha0.
exact xor_0_0.
assume Ha1: a = 1.
rewrite Ha1.
exact xor_1_0.
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

Definition neg : set -> set := fun a => xor a 1.

Theorem neg_0 : neg 0 = 1.
exact xor_0_1.
Qed.

Theorem neg_1 : neg 1 = 0.
exact xor_1_1.
Qed.

Theorem neg_involution : forall a, Bit a -> neg (neg a) = a.
let a.
assume Ha: Bit a.
apply orE (a = 0) (a = 1) (neg (neg a) = a).
assume Ha0: a = 0.
rewrite Ha0.
rewrite neg_0.
exact neg_1.
assume Ha1: a = 1.
rewrite Ha1.
rewrite neg_1.
exact neg_0.
exact bit_cases a Ha.
Qed.

Theorem pairing_lemma : forall a, Bit a -> a <> neg a.
let a.
assume Ha: Bit a.
apply orE (a = 0) (a = 1) (a <> neg a).
assume Ha0: a = 0.
rewrite Ha0.
rewrite neg_0.
exact neq_0_1.
assume Ha1: a = 1.
rewrite Ha1.
rewrite neg_1.
exact neq_1_0.
exact bit_cases a Ha.
Qed.

