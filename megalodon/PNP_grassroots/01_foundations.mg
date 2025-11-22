Infix + 360 right := add_nat.
Infix * 355 right := mul_nat.

Definition one : set := ordsucc 0.
Definition two : set := ordsucc one.
Definition three : set := ordsucc two.
Definition four : set := ordsucc three.
Definition five : set := ordsucc four.

Definition is_bit : set -> prop :=
  fun b => b = 0 \/ b = one.

Definition Bits : set := ordsucc one.

Definition BitString : set -> set -> prop :=
  fun n s => forall i :e n, is_bit (ap s i).

Definition BitStrings : set -> set :=
  fun n => {s :e Bits :^: n | BitString n s}.

Definition bit_at : set -> set -> set :=
  fun s i => ap s i.

Definition zero_vector : set -> set :=
  fun n => fun i :e n => 0.

Definition ones_vector : set -> set :=
  fun n => fun i :e n => one.

Definition basis_vector : set -> set -> set :=
  fun n i => fun j :e n => if j = i then one else 0.

Definition xor : set -> set -> set :=
  fun a b => if a = b then 0 else one.

Definition vec_xor : set -> set -> set -> set :=
  fun n v1 v2 => fun i :e n => xor (ap v1 i) (ap v2 i).

Definition hamming_weight : set -> set -> set :=
  fun n s => nat_primrec 0 (fun i acc => if ap s i = one then ordsucc acc else acc) n.

Definition hamming_dist : set -> set -> set -> set :=
  fun n s1 s2 => nat_primrec 0 (fun i acc => if ap s1 i = ap s2 i then acc else ordsucc acc) n.

Definition SignVector : set -> set -> prop :=
  fun n s => BitString n s.

Definition is_injective : set -> (set -> set) -> prop :=
  fun A f => forall a1 a2 :e A, f a1 = f a2 -> a1 = a2.

Definition is_surjective : set -> set -> (set -> set) -> prop :=
  fun A B f => forall b :e B, exists a :e A, f a = b.

Definition is_bijection : set -> set -> (set -> set) -> prop :=
  fun A B f =>
    (forall a :e A, f a :e B) /\
    is_injective A f /\
    is_surjective A B f.

Definition compose_fun : (set -> set) -> (set -> set) -> (set -> set) :=
  fun g f => fun x => g (f x).

Definition id_fun : set -> (set -> set) :=
  fun A => fun x => x.

Definition SymmetricGroup : set -> set :=
  fun n => {f :e n :^: n | is_bijection n n (fun x => ap f x)}.

Theorem Sn_order : forall n, nat_p n -> equip (nat_factorial n) (SymmetricGroup n).
Admitted.

Definition Z2_power : set -> set := BitStrings.

Theorem Z2n_order : forall n, nat_p n -> equip (exp_nat 2 n) (Z2_power n).
Admitted.

Definition MaskingGroup : set -> set :=
  fun n => {h :e SymmetricGroup n :*: Z2_power n | True}.

Definition mask_perm : set -> set := fun h => ap h 0.
Definition mask_sign : set -> set := fun h => ap h 1.

Definition mask_identity : set -> set :=
  fun n => ((fun i :e n => i), zero_vector n).

Theorem Hn_order : forall n, nat_p n ->
  equip (nat_factorial n * exp_nat 2 n) (MaskingGroup n).
Admitted.

Definition Program : set -> prop :=
  fun p => exists n :e omega, BitString n p.

Definition desc_length : set -> set :=
  fun p => Eps_i (fun n => n :e omega /\ BitString n p).

Definition Programs_upto : set -> set :=
  fun L => {p :e Bits :^: L | desc_length p c= L}.

Theorem count_programs : forall L, nat_p L ->
  equip (exp_nat 2 (ordsucc L)) (Programs_upto L).
Admitted.

Definition UTM_computes : set -> set -> set -> prop :=
  fun p y z => True.

Definition UTM_halts_in : set -> set -> set -> prop :=
  fun p y t => True.

Definition is_polytime : set -> prop :=
  fun p => forall y,
    (exists z, UTM_computes p y z) ->
    exists c :e omega, UTM_halts_in p y (exp_nat (desc_length y) c).

Definition inP : set -> prop :=
  fun L =>
    exists p, Program p /\ is_polytime p /\
    forall x, (x :e L <-> exists z, UTM_computes p x z /\ z = one).

Definition inNP : set -> prop :=
  fun L =>
    exists V c, Program V /\ is_polytime V /\
    forall x,
      (x :e L <->
        exists w, desc_length w c= exp_nat (desc_length x) c /\
                  exists z, UTM_computes V (x, w) z /\ z = one).

Definition NP_complete : set -> prop :=
  fun L =>
    inNP L /\
    forall L', inNP L' ->
      exists red, Program red /\ is_polytime red /\
      forall x, (x :e L' <-> exists y, UTM_computes red x y /\ y :e L).

Definition P_equals_NP : prop :=
  forall L, inNP L -> inP L.

Definition P_neq_NP : prop := ~ P_equals_NP.

Theorem P_neq_NP_equiv :
  P_neq_NP <-> (exists L, NP_complete L /\ ~ inP L).
Admitted.

Definition Probability : set -> prop :=
  fun p => True.

Definition independent_events : set -> set -> prop :=
  fun A B => True.

Definition iid_sequence : set -> (set -> set) -> prop :=
  fun t X => True.

Definition Decoder : set -> prop := Program.

Definition polytime_decoder : set -> prop :=
  fun D => Decoder D /\ is_polytime D.

Definition decoder_succeeds_on : set -> set -> set -> prop :=
  fun D Phi X => exists z, UTM_computes D Phi z /\ z = X.

Definition success_indicator : set -> set -> set -> set :=
  fun D Phi X => if decoder_succeeds_on D Phi X then one else 0.

Definition proj : set -> set -> set := ap.

Definition sum_range : (set -> set) -> set -> set :=
  fun f n => nat_primrec 0 (fun i acc => acc + f i) n.

Definition max_range : (set -> set) -> set -> set :=
  fun f n => nat_primrec 0 (fun i acc => if f i :e acc then acc else f i) n.

Theorem add_nat_zero_r : forall n, nat_p n -> n + 0 = n.
Admitted.

Theorem mul_nat_zero_r : forall n, nat_p n -> n * 0 = 0.
Admitted.

Theorem mul_nat_one_r : forall n, nat_p n -> n * 1 = n.
Admitted.

Theorem exp_nat_zero : forall n, nat_p n -> n <> 0 -> exp_nat n 0 = 1.
Admitted.

Theorem exp_nat_one : forall n, nat_p n -> exp_nat n 1 = n.
Admitted.
