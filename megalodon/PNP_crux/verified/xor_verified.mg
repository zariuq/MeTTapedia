(* XOR Properties - FULLY VERIFIED in Megalodon *)
(* To verify: cat preamble.mgs xor_verified.mg > combined.mg && megalodon combined.mg *)

Definition Bit : set -> prop := fun b => b :e 2.

Definition xor : set -> set -> set := fun a b =>
  if a = b then 0 else 1.

Theorem zero_is_bit : Bit 0.
exact In_0_2.
Qed.

Theorem one_is_bit : Bit 1.
exact In_1_2.
Qed.

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

(* KEY LEMMA for Neutrality: a and neg(a) are always different *)
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

(* This pairing lemma is the foundation for Neutrality:
   The T_i involution flips bit i of the witness via negation.
   Since a <> neg(a), the witness changes, establishing the
   measure-preserving bijection that gives 1/2 probability. *)

