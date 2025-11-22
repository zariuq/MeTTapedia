(* P ≠ NP Foundations - Builds on 00_preamble.mg *)
(* Requires: megalodon -I examples/mizar/PfgMizarNov2020Preamble.mgs 00_preamble.mg *)

(* ========================================================================= *)
(* Matrix algebra over F_2 and linear algebra foundations                    *)
(* ========================================================================= *)

(* --- Matrices over F_2 --- *)

(* A k×m matrix over F_2 is a function from k to (m -> Bits) *)
Definition Matrix : set -> set -> set -> prop :=
  fun rows cols A =>
    forall i :e rows, forall j :e cols, ap (ap A i) j :e Bits.

(* The set of k×m matrices *)
Definition Matrices : set -> set -> set :=
  fun k m => Sep ((Bits :^: m) :^: k) (Matrix k m).

(* Matrix entry access *)
Definition mat_entry : set -> set -> set -> set :=
  fun A i j => ap (ap A i) j.

(* Zero matrix *)
Definition zero_matrix : set -> set -> set :=
  fun rows cols => fun i :e rows => fun j :e cols => 0.

Theorem zero_matrix_is_Matrix : forall k m, nat_p k -> nat_p m ->
  Matrix k m (zero_matrix k m).
let k m. assume Hk: nat_p k. assume Hm: nat_p m.
let i. assume Hi: i :e k.
let j. assume Hj: j :e m.
prove ap (ap (zero_matrix k m) i) j :e Bits.
prove ap (ap (fun r :e k => fun c :e m => 0) i) j :e Bits.
rewrite beta k (fun r => fun c :e m => 0) i Hi.
rewrite beta m (fun c => 0) j Hj.
prove 0 :e Bits.
exact In_0_2.
Qed.

(* Identity matrix *)
Definition identity_matrix : set -> set :=
  fun n => fun i :e n => fun j :e n => if i = j then 1 else 0.

(* Matrix row extraction *)
Definition matrix_row : set -> set -> set :=
  fun A i => ap A i.

(* Matrix column extraction (requires row count k) *)
Definition matrix_col : set -> set -> set -> set :=
  fun k A j => fun i :e k => ap (ap A i) j.

(* --- Bit-wise AND --- *)

Definition bit_and : set -> set -> set :=
  fun a b => if a = 1 /\ b = 1 then 1 else 0.

Theorem bit_and_0_0 : bit_and 0 0 = 0.
prove (if 0 = 1 /\ 0 = 1 then 1 else 0) = 0.
claim L: ~(0 = 1 /\ 0 = 1).
{ assume H. apply H. assume H1: 0 = 1. exact (neq_0_1 H1). }
exact (If_i_0 (0 = 1 /\ 0 = 1) 1 0 L).
Qed.

Theorem bit_and_0_1 : bit_and 0 1 = 0.
prove (if 0 = 1 /\ 1 = 1 then 1 else 0) = 0.
claim L: ~(0 = 1 /\ 1 = 1).
{ assume H. apply H. assume H1: 0 = 1. exact (neq_0_1 H1). }
exact (If_i_0 (0 = 1 /\ 1 = 1) 1 0 L).
Qed.

Theorem bit_and_1_0 : bit_and 1 0 = 0.
prove (if 1 = 1 /\ 0 = 1 then 1 else 0) = 0.
claim L: ~(1 = 1 /\ 0 = 1).
{ assume H. apply H. assume _ H1: 0 = 1. exact (neq_0_1 H1). }
exact (If_i_0 (1 = 1 /\ 0 = 1) 1 0 L).
Qed.

Theorem bit_and_1_1 : bit_and 1 1 = 1.
prove (if 1 = 1 /\ 1 = 1 then 1 else 0) = 1.
claim L: 1 = 1 /\ 1 = 1.
{ apply andI. reflexivity. reflexivity. }
exact (If_i_1 (1 = 1 /\ 1 = 1) 1 0 L).
Qed.

Theorem bit_and_is_bit : forall a b, is_bit a -> is_bit b -> is_bit (bit_and a b).
let a b. assume Ha: is_bit a. assume Hb: is_bit b.
apply Ha.
- assume Ha0: a = 0. rewrite Ha0.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0. rewrite bit_and_0_0. exact bit_0.
  + assume Hb1: b = 1. rewrite Hb1. rewrite bit_and_0_1. exact bit_0.
- assume Ha1: a = 1. rewrite Ha1.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0. rewrite bit_and_1_0. exact bit_0.
  + assume Hb1: b = 1. rewrite Hb1. rewrite bit_and_1_1. exact bit_1.
Qed.

Theorem bit_and_comm : forall a b, is_bit a -> is_bit b -> bit_and a b = bit_and b a.
let a b. assume Ha: is_bit a. assume Hb: is_bit b.
apply Ha.
- assume Ha0: a = 0. rewrite Ha0.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0. reflexivity.
  + assume Hb1: b = 1. rewrite Hb1.
    rewrite bit_and_0_1. rewrite bit_and_1_0. reflexivity.
- assume Ha1: a = 1. rewrite Ha1.
  apply Hb.
  + assume Hb0: b = 0. rewrite Hb0.
    rewrite bit_and_1_0. rewrite bit_and_0_1. reflexivity.
  + assume Hb1: b = 1. rewrite Hb1. reflexivity.
Qed.

(* --- Inner Product over F_2 --- *)

(* Inner product computed via primitive recursion *)
Definition inner_product_f2 : set -> set -> set -> set :=
  fun n a b =>
    nat_primrec 0 (fun j acc => xor acc (bit_and (ap a j) (ap b j))) n.

Theorem inner_product_f2_0 : forall a b, inner_product_f2 0 a b = 0.
let a b.
prove nat_primrec 0 (fun j acc => xor acc (bit_and (ap a j) (ap b j))) 0 = 0.
exact (nat_primrec_0 0 (fun j acc => xor acc (bit_and (ap a j) (ap b j)))).
Qed.

Theorem inner_product_f2_S : forall n a b, nat_p n ->
  inner_product_f2 (ordsucc n) a b =
  xor (inner_product_f2 n a b) (bit_and (ap a n) (ap b n)).
let n a b. assume Hn: nat_p n.
prove nat_primrec 0 (fun j acc => xor acc (bit_and (ap a j) (ap b j))) (ordsucc n) =
      xor (inner_product_f2 n a b) (bit_and (ap a n) (ap b n)).
rewrite (nat_primrec_S 0 (fun j acc => xor acc (bit_and (ap a j) (ap b j))) n Hn).
reflexivity.
Qed.

(* --- Matrix-Vector Product --- *)

Definition matrix_vec_prod : set -> set -> set -> set -> set :=
  fun k m A x =>
    fun i :e k => inner_product_f2 m (matrix_row A i) x.

(* Vector addition over F_2 (same as XOR) *)
Definition vec_add_f2 : set -> set -> set -> set := vec_xor.

(* --- Linear Hash Family --- *)

Definition apply_linear_hash : set -> set -> set -> set -> set -> set :=
  fun k m A b x => vec_add_f2 k (matrix_vec_prod k m A x) b.

Definition LinearHashFamily : set -> set -> set :=
  fun k m => Matrices k m :*: (Bits :^: k).

(* ========================================================================= *)
(* Computation and Complexity                                                *)
(* ========================================================================= *)

(* Program: a finite bit string *)
Definition Program : set -> prop :=
  fun p => exists n :e omega, BitString n p.

(* Description length of a program *)
Definition desc_length : set -> set :=
  fun p => the (fun n => n :e omega /\ BitString n p).

(* Set of programs up to length L *)
Definition Programs_upto : set -> set :=
  fun L => {p :e Bits :^: L | desc_length p c= L}.

(* --- Universal Turing Machine abstraction --- *)
(* UTM_computes p y z means program p on input y outputs z *)
Parameter UTM_computes : set -> set -> set -> prop.

(* UTM_halts_in p y t means program p on input y halts within t steps *)
Parameter UTM_halts_in : set -> set -> set -> prop.

(* --- Polynomial Time --- *)

Definition is_polytime : set -> prop :=
  fun p => forall y,
    (exists z, UTM_computes p y z) ->
    exists c :e omega, UTM_halts_in p y (exp_nat (desc_length y) c).

(* ========================================================================= *)
(* Complexity Classes P and NP                                               *)
(* ========================================================================= *)

(* Language in P: decidable in polynomial time *)
Definition inP : set -> prop :=
  fun L =>
    exists p, Program p /\ is_polytime p /\
    forall x, (x :e L <-> exists z, UTM_computes p x z /\ z = 1).

(* Language in NP: verifiable in polynomial time with polynomial witness *)
Definition inNP : set -> prop :=
  fun L =>
    exists V c, Program V /\ is_polytime V /\ c :e omega /\
    forall x,
      (x :e L <->
        exists w, desc_length w c= exp_nat (desc_length x) c /\
                  exists z, UTM_computes V (x, w) z /\ z = 1).

(* NP-completeness *)
Definition NP_complete : set -> prop :=
  fun L =>
    inNP L /\
    forall L', inNP L' ->
      exists red, Program red /\ is_polytime red /\
      forall x, (x :e L' <-> exists y, UTM_computes red x y /\ y :e L).

(* P = NP statement *)
Definition P_equals_NP : prop :=
  forall L, inNP L -> inP L.

(* P ≠ NP statement *)
Definition P_neq_NP : prop := ~P_equals_NP.

(* Key equivalence for the proof *)
Theorem P_neq_NP_equiv :
  P_neq_NP <-> (exists L, NP_complete L /\ ~inP L).
apply iffI.
- assume H: P_neq_NP.
  prove exists L, NP_complete L /\ ~inP L.
  (* This direction requires showing SAT is NP-complete
     and that if P=NP then all NP-complete problems are in P *)
  admit.
- assume H: exists L, NP_complete L /\ ~inP L.
  prove ~P_equals_NP.
  assume Heq: P_equals_NP.
  apply H. let L. assume HL: NP_complete L /\ ~inP L.
  apply HL. assume HLnpc: NP_complete L. assume HLnotP: ~inP L.
  apply HLnotP.
  apply Heq.
  prove inNP L.
  apply HLnpc. assume H1 _. exact H1.
Qed.

(* ========================================================================= *)
(* Hamming Weight and Distance                                               *)
(* ========================================================================= *)

Definition hamming_weight : set -> set -> set :=
  fun n s => nat_primrec 0 (fun i acc => if ap s i = 1 then ordsucc acc else acc) n.

Theorem hamming_weight_0 : forall s, hamming_weight 0 s = 0.
let s.
exact (nat_primrec_0 0 (fun i acc => if ap s i = 1 then ordsucc acc else acc)).
Qed.

Theorem hamming_weight_S : forall n s, nat_p n ->
  hamming_weight (ordsucc n) s =
  if ap s n = 1 then ordsucc (hamming_weight n s) else hamming_weight n s.
let n s. assume Hn: nat_p n.
rewrite (nat_primrec_S 0 (fun i acc => if ap s i = 1 then ordsucc acc else acc) n Hn).
reflexivity.
Qed.

Definition hamming_dist : set -> set -> set -> set :=
  fun n s1 s2 => hamming_weight n (vec_xor n s1 s2).

(* ========================================================================= *)
(* Logarithm (floor, base 2)                                                 *)
(* ========================================================================= *)

(* log2 n = largest k such that 2^k ≤ n *)
Definition log2 : set -> set :=
  fun n => the (fun k =>
    k :e omega /\
    exp_nat 2 k c= n /\
    n :e exp_nat 2 (ordsucc k)).

(* Basic log2 properties would need proofs *)
