(* XOR properties - to be concatenated with preamble *)

(* A bit is an element of 2 = {0, 1} *)
Definition Bit : set -> prop := fun b => b :e 2.

(* XOR operation using if-then-else *)
Definition xor : set -> set -> set := fun a b =>
  if a = b then 0 else 1.

(* Basic theorems *)

Theorem zero_is_bit : Bit 0.
unfold Bit.
exact In_0_2.
Qed.

Theorem one_is_bit : Bit 1.
unfold Bit.
exact In_1_2.
Qed.

Theorem bit_cases : forall b, Bit b -> b = 0 \/ b = 1.
let b.
assume Hb: Bit b.
unfold Bit in Hb.
exact cases_2 b Hb (fun i => i = 0 \/ i = 1) (orIL (0 = 0) (0 = 1) (eqI set 0)) (orIR (1 = 0) (1 = 1) (eqI set 1)).
Qed.

(* XOR 0 0 = 0 *)
Theorem xor_0_0 : xor 0 0 = 0.
unfold xor.
exact If_i_1 (0 = 0) 0 1 (eqI set 0).
Qed.

(* XOR 1 1 = 0 *)
Theorem xor_1_1 : xor 1 1 = 0.
unfold xor.
exact If_i_1 (1 = 1) 0 1 (eqI set 1).
Qed.

(* XOR 0 1 = 1 *)
Theorem xor_0_1 : xor 0 1 = 1.
unfold xor.
exact If_i_0 (0 = 1) 0 1 neq_0_1.
Qed.

(* XOR 1 0 = 1 *)
Theorem xor_1_0 : xor 1 0 = 1.
unfold xor.
exact If_i_0 (1 = 0) 0 1 neq_1_0.
Qed.

(* XOR is self-inverse: a xor a = 0 *)
Theorem xor_self : forall a, Bit a -> xor a a = 0.
let a.
assume Ha: Bit a.
apply bit_cases a Ha.
(* Case a = 0 *)
assume Ha0: a = 0.
rewrite Ha0.
exact xor_0_0.
(* Case a = 1 *)
assume Ha1: a = 1.
rewrite Ha1.
exact xor_1_1.
Qed.

(* Negation as XOR with 1 *)
Definition neg : set -> set := fun a => xor a 1.

Theorem neg_0 : neg 0 = 1.
unfold neg.
exact xor_0_1.
Qed.

Theorem neg_1 : neg 1 = 0.
unfold neg.
exact xor_1_1.
Qed.

(* neg is involution *)
Theorem neg_involution : forall a, Bit a -> neg (neg a) = a.
let a.
assume Ha: Bit a.
apply bit_cases a Ha.
(* Case a = 0 *)
assume Ha0: a = 0.
rewrite Ha0.
rewrite neg_0.
exact neg_1.
(* Case a = 1 *)
assume Ha1: a = 1.
rewrite Ha1.
rewrite neg_1.
exact neg_0.
Qed.

(* Key lemma for neutrality: a and neg a are different *)
Theorem pairing_lemma : forall a, Bit a -> a <> neg a.
let a.
assume Ha: Bit a.
apply bit_cases a Ha.
(* Case a = 0 *)
assume Ha0: a = 0.
rewrite Ha0.
rewrite neg_0.
exact neq_0_1.
(* Case a = 1 *)
assume Ha1: a = 1.
rewrite Ha1.
rewrite neg_1.
exact neq_1_0.
Qed.

