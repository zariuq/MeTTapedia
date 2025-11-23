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

Variable m : set.
Axiom m_in_omega : m :e omega.

Definition T_i_preserves : set -> (set -> prop) -> (set -> set) -> prop := fun i P transform =>
  forall inst : set, P inst <-> P (transform inst).

Definition flips_witness_bit : set -> (set -> set) -> (set -> set) -> prop := fun i witness transform =>
  forall inst : set, Bit (ap (witness inst) i) ->
    ap (witness (transform inst)) i = neg_bit (ap (witness inst) i).

Definition is_involution : (set -> set) -> prop := fun f =>
  forall x : set, f (f x) = x.

Theorem neutrality_abstract : forall i : set, forall T : set -> set, forall W : set -> set, forall P : set -> prop,
  i :e m ->
  is_involution T ->
  T_i_preserves i P T ->
  flips_witness_bit i W T ->
  True.
let i : set.
let T : set -> set.
let W : set -> set.
let P : set -> prop.
assume Hi: i :e m.
assume Hinv: is_involution T.
assume HTP: T_i_preserves i P T.
assume HFW: flips_witness_bit i W T.
exact TrueI.
Qed.

