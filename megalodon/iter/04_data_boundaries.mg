(** ============================================================================
   Iter Native MeTTa Architecture Verification - Module 4
   Data-Is-Never-Code Boundaries:
     1. lib_formalizations.metta: Dyck bracket depth, single-form anti-injection
     2. append_last_transcript_lines.metta: O(K) streaming tail & chunk invariance
     3. alarms.metta: due/future partition soundness & sorted merge invariants
   Checked natively by CeTTa's Megalodon kernel against standard Egal preamble.mgs.
   Zero document axioms. Zero admitted. Zero aby.
   ============================================================================ *)

Section IterDataBoundaries.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

(** ---- Part 1: Natural & Integer Arithmetic Helpers ------------------------ *)

Theorem nat_0_omega : 0 :e omega.
exact nat_p_omega 0 nat_0.
Qed.

Theorem nat_1_omega : 1 :e omega.
exact nat_p_omega 1 nat_1.
Qed.

Theorem nat_add_omega : forall n :e omega, forall m :e omega, n + m :e omega.
let n. assume Hn. let m. assume Hm.
rewrite <- add_nat_add_SNo n Hn m Hm.
exact nat_p_omega (add_nat n m) (add_nat_p n (omega_nat_p n Hn) m (omega_nat_p m Hm)).
Qed.

Theorem nat_mul_omega : forall n :e omega, forall m :e omega, n * m :e omega.
let n. assume Hn. let m. assume Hm.
rewrite <- mul_nat_mul_SNo n Hn m Hm.
exact nat_p_omega (mul_nat n m) (mul_nat_p n (omega_nat_p n Hn) m (omega_nat_p m Hm)).
Qed.

Theorem ordsucc_eq_add_1 : forall n :e omega, ordsucc n = n + 1.
let n. assume Hn.
rewrite <- add_nat_add_SNo n Hn 1 nat_1_omega.
prove ordsucc n = add_nat n (ordsucc 0).
rewrite add_nat_SR n 0 nat_0.
rewrite add_nat_0R n.
reflexivity.
Qed.

Theorem nat_In_SNoLt : forall n :e omega, forall m :e n, m < n.
let n. assume Hn. let m. assume Hm.
exact ordinal_In_SNoLt n (nat_p_ordinal n (omega_nat_p n Hn)) m Hm.
Qed.

Theorem nat_SNoLt_In : forall n :e omega, forall m :e omega, m < n -> m :e n.
let n. assume Hn. let m. assume Hm. assume Hlt.
apply ordinal_trichotomy_or_impred m n (nat_p_ordinal m (omega_nat_p m Hm)) (nat_p_ordinal n (omega_nat_p n Hn)).
- assume H : m :e n. exact H.
- assume Heq : m = n. apply FalseE. apply SNoLt_irref m. rewrite Heq at 2. exact Hlt.
- assume Hrev : n :e m. apply FalseE.
  exact SNoLt_irref m (SNoLt_tra m n m (omega_SNo m Hm) (omega_SNo n Hn) (omega_SNo m Hm) Hlt (nat_In_SNoLt m Hm n Hrev)).
Qed.

Theorem nat_0_Le : forall n :e omega, 0 <= n.
let n. assume Hn.
apply nat_ind (fun k => 0 <= k).
- exact SNoLe_ref 0.
- let k. assume Hk Hle.
  claim Hko : k :e omega. { exact nat_p_omega k Hk. }
  rewrite ordsucc_eq_add_1 k Hko.
  apply SNoLe_tra 0 k (k + 1) SNo_0 (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) Hle.
  rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
  exact add_SNo_Le2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
- exact omega_nat_p n Hn.
Qed.

Theorem nat_In_omega : forall n :e omega, forall m :e n, m :e omega.
let n. assume Hn. let m. assume Hm.
exact nat_p_omega m (nat_p_trans n (omega_nat_p n Hn) m Hm).
Qed.

Theorem nat_pos_pred : forall n :e omega, 0 < n -> exists k :e omega, n = k + 1.
let n. assume Hn Hpos.
apply nat_inv n (omega_nat_p n Hn).
- assume H0 : n = 0. apply FalseE. apply SNoLt_irref 0. rewrite <- H0 at 2. exact Hpos.
- assume Hex. apply Hex. let k. assume Hk. apply Hk. assume Hkn Heq.
  claim Hko : k :e omega. { exact nat_p_omega k Hkn. }
  witness k. apply andI.
  + exact Hko.
  + rewrite Heq. exact ordsucc_eq_add_1 k Hko.
Qed.

Theorem nat_SNoLt_S_Le : forall m :e omega, forall n :e omega, m < n -> m + 1 <= n.
let m. assume Hm. let n. assume Hn Hlt.
claim Hin : m :e n. { exact nat_SNoLt_In n Hn m Hm Hlt. }
claim Hnpos : 0 < n. { exact SNoLeLt_tra 0 m n SNo_0 (omega_SNo m Hm) (omega_SNo n Hn) (nat_0_Le m Hm) Hlt. }
apply nat_pos_pred n Hn Hnpos. let k. assume Hk. apply Hk. assume Hko Heq.
claim Hmk : m :e ordsucc k. { rewrite ordsucc_eq_add_1 k Hko. rewrite <- Heq. exact Hin. }
claim Hle : m <= k.
{ apply ordsuccE k m Hmk.
  - assume H : m :e k. exact SNoLtLe m k (nat_In_SNoLt k Hko m H).
  - assume H : m = k. rewrite H. exact SNoLe_ref k. }
rewrite Heq.
exact add_SNo_Le1 m 1 k (omega_SNo m Hm) SNo_1 (omega_SNo k Hko) Hle.
Qed.

Theorem nat_Le_or_Lt : forall a :e omega, forall b :e omega, a <= b \/ b < a.
let a. assume Ha. let b. assume Hb.
apply ordinal_trichotomy_or_impred a b (nat_p_ordinal a (omega_nat_p a Ha)) (nat_p_ordinal b (omega_nat_p b Hb)).
- assume H : a :e b. apply orIL. exact SNoLtLe a b (nat_In_SNoLt b Hb a H).
- assume H : a = b. apply orIL. rewrite H. exact SNoLe_ref b.
- assume H : b :e a. apply orIR. exact nat_In_SNoLt a Ha b H.
Qed.

Theorem SNo_add_sub_cancel_1 : forall k m, SNo k -> SNo m -> (k + 1) + - (m + 1) = k + - m.
let k m. assume Hk Hm.
rewrite minus_add_SNo_distr m 1 Hm SNo_1.
rewrite add_SNo_com (- m) (- 1) (SNo_minus_SNo m Hm) (SNo_minus_SNo 1 SNo_1).
rewrite add_SNo_assoc (k + 1) (- 1) (- m) (SNo_add_SNo k 1 Hk SNo_1) (SNo_minus_SNo 1 SNo_1) (SNo_minus_SNo m Hm).
rewrite add_SNo_minus_R2 k 1 Hk SNo_1.
reflexivity.
Qed.

Theorem SNo_add_sub_L : forall a b, SNo a -> SNo b -> b + (a + - b) = a.
let a b. assume Ha Hb.
rewrite add_SNo_com a (- b) Ha (SNo_minus_SNo b Hb).
rewrite add_SNo_assoc b (- b) a Hb (SNo_minus_SNo b Hb) Ha.
rewrite add_SNo_minus_SNo_rinv b Hb.
exact add_SNo_0L a Ha.
Qed.

Theorem SNo_sub_sub : forall a b, SNo a -> SNo b -> a + - (a + - b) = b.
let a b. assume Ha Hb.
rewrite minus_add_SNo_distr a (- b) Ha (SNo_minus_SNo b Hb).
rewrite minus_SNo_invol b Hb.
exact add_SNo_minus_L2' a b Ha Hb.
Qed.

Theorem nat_sub_omega : forall m :e omega, forall n :e omega, m <= n -> n + - m :e omega.
let m. assume Hm.
apply nat_ind (fun k => forall n :e omega, k <= n -> n + - k :e omega).
- let n. assume Hn Hle.
  rewrite minus_SNo_0. rewrite add_SNo_0R n (omega_SNo n Hn). exact Hn.
- let k. assume Hk IH. let n. assume Hn Hle.
  claim Hko : k :e omega. { exact nat_p_omega k Hk. }
  claim Hk1 : ordsucc k = k + 1. { exact ordsucc_eq_add_1 k Hko. }
  claim Hnpos : 0 < n.
  { apply SNoLtLe_tra 0 (k + 1) n SNo_0 (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) (omega_SNo n Hn).
    - apply SNoLeLt_tra 0 k (k + 1) SNo_0 (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) (nat_0_Le k Hko).
      rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
      exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
    - rewrite <- Hk1. exact Hle. }
  apply nat_pos_pred n Hn Hnpos. let p. assume Hp. apply Hp. assume Hpo Hnp.
  claim Hkp : k <= p.
  { apply ordinal_trichotomy_or_impred k p (nat_p_ordinal k Hk) (nat_p_ordinal p (omega_nat_p p Hpo)).
    - assume H1 : k :e p. exact SNoLtLe k p (nat_In_SNoLt p Hpo k H1).
    - assume H1 : k = p. rewrite H1. exact SNoLe_ref p.
    - assume H1 : p :e k. apply FalseE.
      claim Hpk : p + 1 <= k. { exact nat_SNoLt_S_Le p Hpo k Hko (nat_In_SNoLt k Hko p H1). }
      claim Hnk : n < ordsucc k.
      { rewrite Hnp. rewrite Hk1.
        apply SNoLeLt_tra (p + 1) k (k + 1) (SNo_add_SNo p 1 (omega_SNo p Hpo) SNo_1) (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) Hpk.
        rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
        exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1. }
      exact SNoLt_irref n (SNoLtLe_tra n (ordsucc k) n (omega_SNo n Hn) (omega_SNo (ordsucc k) (omega_ordsucc k Hko)) (omega_SNo n Hn) Hnk Hle). }
  rewrite Hnp. rewrite Hk1.
  rewrite SNo_add_sub_cancel_1 p k (omega_SNo p Hpo) (omega_SNo k Hko).
  exact IH p Hpo Hkp.
- exact omega_nat_p m Hm.
Qed.

Theorem SNo_add_Lt_cancel_L : forall c a b, SNo c -> SNo a -> SNo b -> c + a < c + b -> a < b.
let c a b. assume Hc Ha Hb Hlt.
claim H1 : - c + (c + a) = a.
{ rewrite add_SNo_assoc (- c) c a (SNo_minus_SNo c Hc) Hc Ha.
  rewrite add_SNo_minus_SNo_linv c Hc. exact add_SNo_0L a Ha. }
claim H2 : - c + (c + b) = b.
{ rewrite add_SNo_assoc (- c) c b (SNo_minus_SNo c Hc) Hc Hb.
  rewrite add_SNo_minus_SNo_linv c Hc. exact add_SNo_0L b Hb. }
rewrite <- H1. rewrite <- H2.
exact add_SNo_Lt2 (- c) (c + a) (c + b) (SNo_minus_SNo c Hc) (SNo_add_SNo c a Hc Ha) (SNo_add_SNo c b Hc Hb) Hlt.
Qed.

Theorem nat_sub_Le : forall n :e omega, forall d :e omega, d <= n -> n + - d <= n.
let n. assume Hn. let d. assume Hd Hle.
claim Hsub : n + - d :e omega. { exact nat_sub_omega d Hd n Hn Hle. }
rewrite <- SNo_add_sub_L n d (omega_SNo n Hn) (omega_SNo d Hd) at 2.
rewrite <- add_SNo_0L (n + - d) (omega_SNo (n + - d) Hsub) at 1.
exact add_SNo_Le1 0 (n + - d) d SNo_0 (omega_SNo (n + - d) Hsub) (omega_SNo d Hd) (nat_0_Le d Hd).
Qed.

Theorem nat_In_sub_add : forall n :e omega, forall d :e omega, d <= n -> forall i :e n + - d, d + i :e n.
let n. assume Hn. let d. assume Hd Hle. let i. assume Hi.
claim Hsub : n + - d :e omega. { exact nat_sub_omega d Hd n Hn Hle. }
claim Hio : i :e omega. { exact nat_In_omega (n + - d) Hsub i Hi. }
claim Hilt : i < n + - d. { exact nat_In_SNoLt (n + - d) Hsub i Hi. }
apply nat_SNoLt_In n Hn (d + i) (nat_add_omega d Hd i Hio).
rewrite <- SNo_add_sub_L n d (omega_SNo n Hn) (omega_SNo d Hd).
exact add_SNo_Lt2 d i (n + - d) (omega_SNo d Hd) (omega_SNo i Hio) (omega_SNo (n + - d) Hsub) Hilt.
Qed.

Theorem omega_Subq_int : forall n :e omega, n :e int.
let n. assume Hn.
exact binunionI1 omega {- k|k :e omega} n Hn.
Qed.

(** ---- Part 2: Finite Sequences & Concatenation Associativity -------------- *)

Definition Seq : set -> (set -> set) -> set := fun n f => setsum n (fun i :e n => f i).
Definition seq_len : set -> set := fun s => proj0 s.
Definition seq_at : set -> set -> set := fun s i => ap (proj1 s) i.
Definition IsSeq : set -> prop := fun s => seq_len s :e omega /\ s = Seq (seq_len s) (fun i => seq_at s i).

Theorem seq_len_mk : forall n, forall f:set -> set, seq_len (Seq n f) = n.
let n f. exact proj0_pair_eq n (fun i :e n => f i).
Qed.

Theorem seq_at_mk : forall n, forall f:set -> set, forall i :e n, seq_at (Seq n f) i = f i.
let n f. let i. assume Hi.
prove ap (proj1 (setsum n (fun j :e n => f j))) i = f i.
rewrite proj1_pair_eq n (fun j :e n => f j).
exact beta n f i Hi.
Qed.

Theorem IsSeq_mk : forall n :e omega, forall f:set -> set, IsSeq (Seq n f).
let n. assume Hn. let f.
prove seq_len (Seq n f) :e omega /\ Seq n f = Seq (seq_len (Seq n f)) (fun i => seq_at (Seq n f) i).
rewrite seq_len_mk n f.
apply andI.
- exact Hn.
- prove setsum n (fun i :e n => f i) = setsum n (fun i :e n => seq_at (Seq n f) i).
  claim Hlam : (fun i :e n => f i) = (fun i :e n => seq_at (Seq n f) i).
  { apply lam_ext n. let i. assume Hi. symmetry. exact seq_at_mk n f i Hi. }
  rewrite Hlam. reflexivity.
Qed.

Theorem seq_ext : forall s1 s2, IsSeq s1 -> IsSeq s2 ->
  seq_len s1 = seq_len s2 ->
  (forall i :e seq_len s1, seq_at s1 i = seq_at s2 i) ->
  s1 = s2.
let s1 s2. assume H1 H2 Hlen Hat.
apply H1. assume Hn1 Heq1. apply H2. assume Hn2 Heq2.
rewrite Heq1. rewrite Heq2.
prove setsum (seq_len s1) (fun i :e seq_len s1 => seq_at s1 i)
    = setsum (seq_len s2) (fun i :e seq_len s2 => seq_at s2 i).
claim Hlam : (fun i :e seq_len s1 => seq_at s1 i) = (fun i :e seq_len s2 => seq_at s2 i).
{ rewrite <- Hlen. apply lam_ext (seq_len s1). exact Hat. }
rewrite Hlam. rewrite Hlen. reflexivity.
Qed.

Definition seq_drop : set -> set -> set :=
  fun d s => Seq (seq_len s + - d) (fun i => seq_at s (d + i)).

Definition seq_concat : set -> set -> set :=
  fun s t => Seq (seq_len s + seq_len t)
    (fun i => if i < seq_len s then seq_at s i else seq_at t (i + - seq_len s)).

Theorem seq_concat_IsSeq : forall s t, IsSeq s -> IsSeq t -> IsSeq (seq_concat s t).
let s t. assume Hs Ht. apply Hs. assume Hsn _. apply Ht. assume Htn _.
exact IsSeq_mk (seq_len s + seq_len t) (nat_add_omega (seq_len s) Hsn (seq_len t) Htn)
      (fun i => if i < seq_len s then seq_at s i else seq_at t (i + - seq_len s)).
Qed.

Theorem seq_concat_len : forall s t, seq_len (seq_concat s t) = seq_len s + seq_len t.
let s t.
exact seq_len_mk (seq_len s + seq_len t)
      (fun i => if i < seq_len s then seq_at s i else seq_at t (i + - seq_len s)).
Qed.

Theorem seq_concat_at_L : forall s t, IsSeq s -> IsSeq t -> forall i :e seq_len s,
  seq_at (seq_concat s t) i = seq_at s i.
let s t. assume Hs Ht. apply Hs. assume Hsn _. apply Ht. assume Htn _.
let i. assume Hi.
claim Hio : i :e omega. { exact nat_In_omega (seq_len s) Hsn i Hi. }
claim Hilt : i < seq_len s. { exact nat_In_SNoLt (seq_len s) Hsn i Hi. }
claim Hic : i :e seq_len s + seq_len t.
{ apply nat_SNoLt_In (seq_len s + seq_len t) (nat_add_omega (seq_len s) Hsn (seq_len t) Htn) i Hio.
  apply SNoLtLe_tra i (seq_len s) (seq_len s + seq_len t) (omega_SNo i Hio) (omega_SNo (seq_len s) Hsn)
        (omega_SNo (seq_len s + seq_len t) (nat_add_omega (seq_len s) Hsn (seq_len t) Htn)) Hilt.
  rewrite <- add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hsn) at 1.
  exact add_SNo_Le2 (seq_len s) 0 (seq_len t) (omega_SNo (seq_len s) Hsn) SNo_0 (omega_SNo (seq_len t) Htn) (nat_0_Le (seq_len t) Htn). }
prove seq_at (Seq (seq_len s + seq_len t) (fun j => if j < seq_len s then seq_at s j else seq_at t (j + - seq_len s))) i = seq_at s i.
rewrite seq_at_mk (seq_len s + seq_len t) (fun j => if j < seq_len s then seq_at s j else seq_at t (j + - seq_len s)) i Hic.
exact If_i_1 (i < seq_len s) (seq_at s i) (seq_at t (i + - seq_len s)) Hilt.
Qed.

Theorem seq_concat_at_R : forall s t, IsSeq s -> IsSeq t -> forall j :e seq_len t,
  seq_at (seq_concat s t) (seq_len s + j) = seq_at t j.
let s t. assume Hs Ht. apply Hs. assume Hsn _. apply Ht. assume Htn _.
let j. assume Hj.
claim Hjo : j :e omega. { exact nat_In_omega (seq_len t) Htn j Hj. }
claim Hic : seq_len s + j :e seq_len s + seq_len t.
{ apply nat_SNoLt_In (seq_len s + seq_len t) (nat_add_omega (seq_len s) Hsn (seq_len t) Htn) (seq_len s + j) (nat_add_omega (seq_len s) Hsn j Hjo).
  exact add_SNo_Lt2 (seq_len s) j (seq_len t) (omega_SNo (seq_len s) Hsn) (omega_SNo j Hjo) (omega_SNo (seq_len t) Htn) (nat_In_SNoLt (seq_len t) Htn j Hj). }
claim Hnlt : ~(seq_len s + j < seq_len s).
{ assume Hlt : seq_len s + j < seq_len s.
  claim Hle : seq_len s <= seq_len s + j.
  { rewrite <- add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hsn) at 1.
    exact add_SNo_Le2 (seq_len s) 0 j (omega_SNo (seq_len s) Hsn) SNo_0 (omega_SNo j Hjo) (nat_0_Le j Hjo). }
  exact SNoLt_irref (seq_len s) (SNoLeLt_tra (seq_len s) (seq_len s + j) (seq_len s)
        (omega_SNo (seq_len s) Hsn) (omega_SNo (seq_len s + j) (nat_add_omega (seq_len s) Hsn j Hjo)) (omega_SNo (seq_len s) Hsn) Hle Hlt). }
prove seq_at (Seq (seq_len s + seq_len t) (fun u => if u < seq_len s then seq_at s u else seq_at t (u + - seq_len s))) (seq_len s + j) = seq_at t j.
rewrite seq_at_mk (seq_len s + seq_len t) (fun u => if u < seq_len s then seq_at s u else seq_at t (u + - seq_len s)) (seq_len s + j) Hic.
rewrite If_i_0 (seq_len s + j < seq_len s) (seq_at s (seq_len s + j)) (seq_at t ((seq_len s + j) + - seq_len s)) Hnlt.
rewrite add_SNo_com (seq_len s) j (omega_SNo (seq_len s) Hsn) (omega_SNo j Hjo).
rewrite add_SNo_minus_R2 j (seq_len s) (omega_SNo j Hjo) (omega_SNo (seq_len s) Hsn).
reflexivity.
Qed.

Theorem seq_concat_assoc : forall a b c, IsSeq a -> IsSeq b -> IsSeq c ->
  seq_concat (seq_concat a b) c = seq_concat a (seq_concat b c).
let a b c. assume Ha Hb Hc.
apply Ha. assume Han _. apply Hb. assume Hbn _. apply Hc. assume Hcn _.
claim Hab : IsSeq (seq_concat a b). { exact seq_concat_IsSeq a b Ha Hb. }
claim Hbc : IsSeq (seq_concat b c). { exact seq_concat_IsSeq b c Hb Hc. }
apply seq_ext (seq_concat (seq_concat a b) c) (seq_concat a (seq_concat b c))
      (seq_concat_IsSeq (seq_concat a b) c Hab Hc) (seq_concat_IsSeq a (seq_concat b c) Ha Hbc).
- rewrite seq_concat_len (seq_concat a b) c.
  rewrite seq_concat_len a b.
  rewrite seq_concat_len a (seq_concat b c).
  rewrite seq_concat_len b c.
  symmetry. exact add_SNo_assoc (seq_len a) (seq_len b) (seq_len c) (omega_SNo (seq_len a) Han) (omega_SNo (seq_len b) Hbn) (omega_SNo (seq_len c) Hcn).
- let i. assume Hi.
  claim Hi_abc : i :e (seq_len a + seq_len b) + seq_len c.
  { rewrite <- seq_concat_len a b. rewrite <- seq_concat_len (seq_concat a b) c. exact Hi. }
  claim Hio : i :e omega.
  { exact nat_In_omega ((seq_len a + seq_len b) + seq_len c)
          (nat_add_omega (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn) (seq_len c) Hcn) i Hi_abc. }
  apply nat_Le_or_Lt (seq_len a) Han i Hio.
  + assume Hage : seq_len a <= i.
    claim Hi_sub_a : i + - seq_len a :e omega. { exact nat_sub_omega (seq_len a) Han i Hio Hage. }
    claim Hia_eq : i = seq_len a + (i + - seq_len a).
    { symmetry. exact SNo_add_sub_L i (seq_len a) (omega_SNo i Hio) (omega_SNo (seq_len a) Han). }
    apply nat_Le_or_Lt (seq_len b) Hbn (i + - seq_len a) Hi_sub_a.
    * assume Hbge : seq_len b <= i + - seq_len a.
      claim Hi_sub_ab : (i + - seq_len a) + - seq_len b :e omega.
      { exact nat_sub_omega (seq_len b) Hbn (i + - seq_len a) Hi_sub_a Hbge. }
      claim Hsub_eq : (i + - seq_len a) + - seq_len b = i + - (seq_len a + seq_len b).
      { rewrite minus_add_SNo_distr (seq_len a) (seq_len b) (omega_SNo (seq_len a) Han) (omega_SNo (seq_len b) Hbn).
        symmetry. exact add_SNo_assoc i (- seq_len a) (- seq_len b) (omega_SNo i Hio) (SNo_minus_SNo (seq_len a) (omega_SNo (seq_len a) Han)) (SNo_minus_SNo (seq_len b) (omega_SNo (seq_len b) Hbn)). }
      claim Hk_in_c : (i + - seq_len a) + - seq_len b :e seq_len c.
      { apply nat_SNoLt_In (seq_len c) Hcn ((i + - seq_len a) + - seq_len b) Hi_sub_ab.
        apply SNo_add_Lt_cancel_L (seq_len a + seq_len b) ((i + - seq_len a) + - seq_len b) (seq_len c)
              (omega_SNo (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn))
              (omega_SNo ((i + - seq_len a) + - seq_len b) Hi_sub_ab) (omega_SNo (seq_len c) Hcn).
        rewrite Hsub_eq.
        rewrite SNo_add_sub_L i (seq_len a + seq_len b) (omega_SNo i Hio) (omega_SNo (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn)).
        exact nat_In_SNoLt ((seq_len a + seq_len b) + seq_len c)
              (nat_add_omega (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn) (seq_len c) Hcn) i Hi_abc. }
      claim Hi_ab_k : i = seq_len (seq_concat a b) + ((i + - seq_len a) + - seq_len b).
      { rewrite seq_concat_len a b. rewrite Hsub_eq.
        symmetry. exact SNo_add_sub_L i (seq_len a + seq_len b) (omega_SNo i Hio) (omega_SNo (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn)). }
      claim Hia_bk : i + - seq_len a = seq_len b + ((i + - seq_len a) + - seq_len b).
      { symmetry. exact SNo_add_sub_L (i + - seq_len a) (seq_len b) (omega_SNo (i + - seq_len a) Hi_sub_a) (omega_SNo (seq_len b) Hbn). }
      claim Hia_in_bc : i + - seq_len a :e seq_len (seq_concat b c).
      { rewrite seq_concat_len b c. rewrite Hia_bk.
        apply nat_SNoLt_In (seq_len b + seq_len c) (nat_add_omega (seq_len b) Hbn (seq_len c) Hcn)
              (seq_len b + ((i + - seq_len a) + - seq_len b)) (nat_add_omega (seq_len b) Hbn ((i + - seq_len a) + - seq_len b) Hi_sub_ab).
        exact add_SNo_Lt2 (seq_len b) ((i + - seq_len a) + - seq_len b) (seq_len c) (omega_SNo (seq_len b) Hbn)
              (omega_SNo ((i + - seq_len a) + - seq_len b) Hi_sub_ab) (omega_SNo (seq_len c) Hcn) (nat_In_SNoLt (seq_len c) Hcn ((i + - seq_len a) + - seq_len b) Hk_in_c). }
      claim HL : seq_at (seq_concat (seq_concat a b) c) i = seq_at c ((i + - seq_len a) + - seq_len b).
      { rewrite Hi_ab_k at 1.
        exact seq_concat_at_R (seq_concat a b) c Hab Hc ((i + - seq_len a) + - seq_len b) Hk_in_c. }
      claim HR : seq_at (seq_concat a (seq_concat b c)) i = seq_at c ((i + - seq_len a) + - seq_len b).
      { rewrite Hia_eq at 1.
        rewrite seq_concat_at_R a (seq_concat b c) Ha Hbc (i + - seq_len a) Hia_in_bc.
        rewrite Hia_bk at 1.
        exact seq_concat_at_R b c Hb Hc ((i + - seq_len a) + - seq_len b) Hk_in_c. }
      rewrite HL. rewrite HR. reflexivity.
    * assume Hblt : i + - seq_len a < seq_len b.
      claim Hia_in_b : i + - seq_len a :e seq_len b. { exact nat_SNoLt_In (seq_len b) Hbn (i + - seq_len a) Hi_sub_a Hblt. }
      claim Hi_in_ab : i :e seq_len (seq_concat a b).
      { rewrite seq_concat_len a b. rewrite Hia_eq.
        apply nat_SNoLt_In (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn)
              (seq_len a + (i + - seq_len a)) (nat_add_omega (seq_len a) Han (i + - seq_len a) Hi_sub_a).
        exact add_SNo_Lt2 (seq_len a) (i + - seq_len a) (seq_len b) (omega_SNo (seq_len a) Han) (omega_SNo (i + - seq_len a) Hi_sub_a) (omega_SNo (seq_len b) Hbn) Hblt. }
      claim Hia_in_bc : i + - seq_len a :e seq_len (seq_concat b c).
      { rewrite seq_concat_len b c.
        apply nat_SNoLt_In (seq_len b + seq_len c) (nat_add_omega (seq_len b) Hbn (seq_len c) Hcn) (i + - seq_len a) Hi_sub_a.
        apply SNoLtLe_tra (i + - seq_len a) (seq_len b) (seq_len b + seq_len c) (omega_SNo (i + - seq_len a) Hi_sub_a) (omega_SNo (seq_len b) Hbn)
              (omega_SNo (seq_len b + seq_len c) (nat_add_omega (seq_len b) Hbn (seq_len c) Hcn)) Hblt.
        rewrite <- add_SNo_0R (seq_len b) (omega_SNo (seq_len b) Hbn) at 1.
        exact add_SNo_Le2 (seq_len b) 0 (seq_len c) (omega_SNo (seq_len b) Hbn) SNo_0 (omega_SNo (seq_len c) Hcn) (nat_0_Le (seq_len c) Hcn). }
      rewrite seq_concat_at_L (seq_concat a b) c Hab Hc i Hi_in_ab.
      rewrite Hia_eq.
      rewrite seq_concat_at_R a b Ha Hb (i + - seq_len a) Hia_in_b.
      rewrite seq_concat_at_R a (seq_concat b c) Ha Hbc (i + - seq_len a) Hia_in_bc.
      rewrite seq_concat_at_L b c Hb Hc (i + - seq_len a) Hia_in_b.
      reflexivity.
  + assume Halt : i < seq_len a.
    claim Hi_a : i :e seq_len a. { exact nat_SNoLt_In (seq_len a) Han i Hio Halt. }
    claim Hi_ab : i :e seq_len (seq_concat a b).
    { rewrite seq_concat_len a b.
      apply nat_SNoLt_In (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn) i Hio.
      apply SNoLtLe_tra i (seq_len a) (seq_len a + seq_len b) (omega_SNo i Hio) (omega_SNo (seq_len a) Han)
            (omega_SNo (seq_len a + seq_len b) (nat_add_omega (seq_len a) Han (seq_len b) Hbn)) Halt.
      rewrite <- add_SNo_0R (seq_len a) (omega_SNo (seq_len a) Han) at 1.
      exact add_SNo_Le2 (seq_len a) 0 (seq_len b) (omega_SNo (seq_len a) Han) SNo_0 (omega_SNo (seq_len b) Hbn) (nat_0_Le (seq_len b) Hbn). }
    rewrite seq_concat_at_L (seq_concat a b) c Hab Hc i Hi_ab.
    rewrite seq_concat_at_L a b Ha Hb i Hi_a.
    rewrite seq_concat_at_L a (seq_concat b c) Ha Hbc i Hi_a.
    reflexivity.
Qed.

(** ---- Part 3: lib_formalizations.metta Dyck Depth & Anti-Injection -------- *)

Definition LPAREN : set := 4 * 10.
Definition RPAREN : set := 4 * 10 + 1.
Definition DQUOTE : set := 3 * 10 + 4.

Theorem LPAREN_neq_RPAREN : LPAREN <> RPAREN.
claim H40o : LPAREN :e omega. { exact nat_mul_omega 4 (nat_p_omega 4 nat_4) 10 (nat_p_omega 10 nat_10). }
assume Heq : LPAREN = LPAREN + 1.
apply SNoLt_irref LPAREN.
rewrite Heq at 2.
rewrite <- add_SNo_0R LPAREN (omega_SNo LPAREN H40o) at 1.
exact add_SNo_Lt2 LPAREN 0 1 (omega_SNo LPAREN H40o) SNo_0 SNo_1 SNoLt_0_1.
Qed.

Definition paren_delta : set -> set :=
  fun c => if c = LPAREN then 1 else if c = RPAREN then - 1 else 0.

Theorem paren_delta_int : forall c, paren_delta c :e int.
let c.
apply xm (c = LPAREN).
- assume H : c = LPAREN.
  prove (if c = LPAREN then 1 else if c = RPAREN then - 1 else 0) :e int.
  rewrite If_i_1 (c = LPAREN) 1 (if c = RPAREN then - 1 else 0) H.
  exact omega_Subq_int 1 nat_1_omega.
- assume Hnl : c <> LPAREN.
  prove (if c = LPAREN then 1 else if c = RPAREN then - 1 else 0) :e int.
  rewrite If_i_0 (c = LPAREN) 1 (if c = RPAREN then - 1 else 0) Hnl.
  apply xm (c = RPAREN).
  + assume Hr : c = RPAREN.
    rewrite If_i_1 (c = RPAREN) (- 1) 0 Hr.
    exact int_minus_SNo_omega 1 nat_1_omega.
  + assume Hnr : c <> RPAREN.
    rewrite If_i_0 (c = RPAREN) (- 1) 0 Hnr.
    exact omega_Subq_int 0 nat_0_omega.
Qed.

Definition prefix_depth : set -> set -> set :=
  fun s k => nat_primrec 0 (fun j d => d + paren_delta (seq_at s j)) k.

Theorem prefix_depth_0 : forall s, prefix_depth s 0 = 0.
let s. exact nat_primrec_0 0 (fun j d => d + paren_delta (seq_at s j)).
Qed.

Theorem prefix_depth_S : forall s, forall k :e omega,
  prefix_depth s (k + 1) = prefix_depth s k + paren_delta (seq_at s k).
let s. let k. assume Hk.
rewrite <- ordsucc_eq_add_1 k Hk.
exact nat_primrec_S 0 (fun j d => d + paren_delta (seq_at s j)) k (omega_nat_p k Hk).
Qed.

Theorem prefix_depth_int : forall s, forall k :e omega, prefix_depth s k :e int.
let s. let k. assume Hk.
apply nat_ind (fun m => prefix_depth s m :e int).
- prove prefix_depth s 0 :e int.
  rewrite prefix_depth_0 s. exact omega_Subq_int 0 nat_0_omega.
- let m. assume Hm IH.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  prove prefix_depth s (ordsucc m) :e int.
  rewrite ordsucc_eq_add_1 m Hmo.
  rewrite prefix_depth_S s m Hmo.
  exact int_add_SNo (prefix_depth s m) IH (paren_delta (seq_at s m)) (paren_delta_int (seq_at s m)).
- exact omega_nat_p k Hk.
Qed.

Theorem prefix_depth_concat_L : forall s1 s2, IsSeq s1 -> IsSeq s2 ->
  forall k :e omega, k <= seq_len s1 ->
  prefix_depth (seq_concat s1 s2) k = prefix_depth s1 k.
let s1 s2. assume H1 H2.
apply H1. assume Hn1 _.
let k. assume Hk.
apply nat_ind (fun m => m <= seq_len s1 -> prefix_depth (seq_concat s1 s2) m = prefix_depth s1 m).
- assume _. rewrite prefix_depth_0 (seq_concat s1 s2). rewrite prefix_depth_0 s1. reflexivity.
- let m. assume Hm IH Hle.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  claim Hm1 : ordsucc m = m + 1. { exact ordsucc_eq_add_1 m Hmo. }
  claim Hmlt : m < seq_len s1.
  { apply SNoLtLe_tra m (m + 1) (seq_len s1) (omega_SNo m Hmo) (SNo_add_SNo m 1 (omega_SNo m Hmo) SNo_1) (omega_SNo (seq_len s1) Hn1).
    - rewrite <- add_SNo_0R m (omega_SNo m Hmo) at 1.
      exact add_SNo_Lt2 m 0 1 (omega_SNo m Hmo) SNo_0 SNo_1 SNoLt_0_1.
    - rewrite <- Hm1. exact Hle. }
  claim Hmin : m :e seq_len s1. { exact nat_SNoLt_In (seq_len s1) Hn1 m Hmo Hmlt. }
  rewrite Hm1.
  rewrite prefix_depth_S (seq_concat s1 s2) m Hmo.
  rewrite prefix_depth_S s1 m Hmo.
  rewrite IH (SNoLtLe m (seq_len s1) Hmlt).
  rewrite seq_concat_at_L s1 s2 H1 H2 m Hmin.
  reflexivity.
- exact omega_nat_p k Hk.
Qed.

Theorem prefix_depth_concat_R : forall s1 s2, IsSeq s1 -> IsSeq s2 ->
  forall m :e omega, m <= seq_len s2 ->
  prefix_depth (seq_concat s1 s2) (seq_len s1 + m) = prefix_depth s1 (seq_len s1) + prefix_depth s2 m.
let s1 s2. assume H1 H2.
apply H1. assume Hn1 _. apply H2. assume Hn2 _.
let m. assume Hm.
apply nat_ind (fun j => j <= seq_len s2 -> prefix_depth (seq_concat s1 s2) (seq_len s1 + j) = prefix_depth s1 (seq_len s1) + prefix_depth s2 j).
- assume _.
  rewrite add_SNo_0R (seq_len s1) (omega_SNo (seq_len s1) Hn1).
  rewrite prefix_depth_0 s2.
  rewrite add_SNo_0R (prefix_depth s1 (seq_len s1)) (int_SNo (prefix_depth s1 (seq_len s1)) (prefix_depth_int s1 (seq_len s1) Hn1)).
  exact prefix_depth_concat_L s1 s2 H1 H2 (seq_len s1) Hn1 (SNoLe_ref (seq_len s1)).
- let j. assume Hj IH Hle.
  claim Hjo : j :e omega. { exact nat_p_omega j Hj. }
  claim Hj1 : ordsucc j = j + 1. { exact ordsucc_eq_add_1 j Hjo. }
  claim Hjlt : j < seq_len s2.
  { apply SNoLtLe_tra j (j + 1) (seq_len s2) (omega_SNo j Hjo) (SNo_add_SNo j 1 (omega_SNo j Hjo) SNo_1) (omega_SNo (seq_len s2) Hn2).
    - rewrite <- add_SNo_0R j (omega_SNo j Hjo) at 1.
      exact add_SNo_Lt2 j 0 1 (omega_SNo j Hjo) SNo_0 SNo_1 SNoLt_0_1.
    - rewrite <- Hj1. exact Hle. }
  claim Hjin : j :e seq_len s2. { exact nat_SNoLt_In (seq_len s2) Hn2 j Hjo Hjlt. }
  rewrite Hj1.
  rewrite add_SNo_assoc (seq_len s1) j 1 (omega_SNo (seq_len s1) Hn1) (omega_SNo j Hjo) SNo_1.
  rewrite prefix_depth_S (seq_concat s1 s2) (seq_len s1 + j) (nat_add_omega (seq_len s1) Hn1 j Hjo).
  rewrite prefix_depth_S s2 j Hjo.
  rewrite IH (SNoLtLe j (seq_len s2) Hjlt).
  rewrite seq_concat_at_R s1 s2 H1 H2 j Hjin.
  symmetry.
  exact add_SNo_assoc (prefix_depth s1 (seq_len s1)) (prefix_depth s2 j) (paren_delta (seq_at s2 j))
        (int_SNo (prefix_depth s1 (seq_len s1)) (prefix_depth_int s1 (seq_len s1) Hn1))
        (int_SNo (prefix_depth s2 j) (prefix_depth_int s2 j Hjo))
        (int_SNo (paren_delta (seq_at s2 j)) (paren_delta_int (seq_at s2 j))).
- exact omega_nat_p m Hm.
Qed.

Definition FormsBalanced : set -> prop :=
  fun s => prefix_depth s (seq_len s) = 0.

Definition FormsSingle : set -> prop :=
  fun s => FormsBalanced s /\
    (forall i :e seq_len s, seq_at s i = RPAREN -> prefix_depth s (i + 1) = 0 -> i + 1 = seq_len s).

Definition QuoteFree : set -> prop :=
  fun s => forall i :e seq_len s, seq_at s i <> DQUOTE.

Definition FormsValid : set -> prop :=
  fun s =>
    0 < seq_len s /\
    seq_at s 0 = LPAREN /\
    (exists k :e omega, seq_len s = k + 1 /\ seq_at s k = RPAREN) /\
    QuoteFree s /\
    FormsSingle s.

Theorem forms_balanced_concat : forall s1 s2, IsSeq s1 -> IsSeq s2 ->
  FormsBalanced s1 -> FormsBalanced s2 -> FormsBalanced (seq_concat s1 s2).
let s1 s2. assume H1 H2 Hb1 Hb2.
apply H1. assume Hn1 _. apply H2. assume Hn2 _.
claim Hb1' : prefix_depth s1 (seq_len s1) = 0. { exact Hb1. }
claim Hb2' : prefix_depth s2 (seq_len s2) = 0. { exact Hb2. }
prove prefix_depth (seq_concat s1 s2) (seq_len (seq_concat s1 s2)) = 0.
rewrite seq_concat_len s1 s2.
rewrite prefix_depth_concat_R s1 s2 H1 H2 (seq_len s2) Hn2 (SNoLe_ref (seq_len s2)).
rewrite Hb1'. rewrite Hb2'.
exact add_SNo_0L 0 SNo_0.
Qed.

(** ANTI-INJECTION THEOREM (lib_formalizations.metta:8-13):
    Whenever s1 is a valid single S-expression (closing at its last char RPAREN
    with net depth 0) and s2 is ANY nonempty trailing sequence, forms:depth with
    single=true rejects s1 ++ s2! Thus multi-form injection "(a) (evil)" is
    structurally impossible through forms:valid. *)
Theorem forms_single_rejects_split_injection : forall s1 s2,
  IsSeq s1 -> IsSeq s2 -> FormsValid s1 -> 0 < seq_len s2 ->
  ~(FormsSingle (seq_concat s1 s2)).
let s1 s2. assume H1 H2 Hv1 Hpos2 Hsingle.
apply H1. assume Hn1 _. apply H2. assume Hn2 _.
apply Hv1. assume Hv1_a Hs1. apply Hv1_a. assume Hv1_b _. apply Hv1_b. assume Hv1_c Hex1.
apply Hs1. assume Hb1 _.
apply Hex1. let k. assume Hk. apply Hk. assume Hko Hk2. apply Hk2. assume Hlen1 Hrp1.
apply Hsingle. assume _ Hno_early.
claim Hk_in_1 : k :e seq_len s1.
{ apply nat_SNoLt_In (seq_len s1) Hn1 k Hko.
  rewrite Hlen1. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
  exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1. }
claim Hk_in_cat : k :e seq_len (seq_concat s1 s2).
{ rewrite seq_concat_len s1 s2.
  apply nat_SNoLt_In (seq_len s1 + seq_len s2) (nat_add_omega (seq_len s1) Hn1 (seq_len s2) Hn2) k Hko.
  apply SNoLtLe_tra k (seq_len s1) (seq_len s1 + seq_len s2) (omega_SNo k Hko) (omega_SNo (seq_len s1) Hn1)
        (omega_SNo (seq_len s1 + seq_len s2) (nat_add_omega (seq_len s1) Hn1 (seq_len s2) Hn2))
        (nat_In_SNoLt (seq_len s1) Hn1 k Hk_in_1).
  rewrite <- add_SNo_0R (seq_len s1) (omega_SNo (seq_len s1) Hn1) at 1.
  exact add_SNo_Le2 (seq_len s1) 0 (seq_len s2) (omega_SNo (seq_len s1) Hn1) SNo_0 (omega_SNo (seq_len s2) Hn2) (nat_0_Le (seq_len s2) Hn2). }
claim Hat_rp : seq_at (seq_concat s1 s2) k = RPAREN.
{ rewrite seq_concat_at_L s1 s2 H1 H2 k Hk_in_1. exact Hrp1. }
claim Hdep0 : prefix_depth (seq_concat s1 s2) (k + 1) = 0.
{ rewrite <- Hlen1.
  rewrite prefix_depth_concat_L s1 s2 H1 H2 (seq_len s1) Hn1 (SNoLe_ref (seq_len s1)).
  exact Hb1. }
claim Heq_len : k + 1 = seq_len (seq_concat s1 s2).
{ exact Hno_early k Hk_in_cat Hat_rp Hdep0. }
apply SNoLt_irref (seq_len s1).
claim Hlt_cat : seq_len s1 < seq_len s1 + seq_len s2.
{ rewrite <- add_SNo_0R (seq_len s1) (omega_SNo (seq_len s1) Hn1) at 1.
  exact add_SNo_Lt2 (seq_len s1) 0 (seq_len s2) (omega_SNo (seq_len s1) Hn1) SNo_0 (omega_SNo (seq_len s2) Hn2) Hpos2. }
claim Hn1_eq : seq_len s1 = seq_len s1 + seq_len s2.
{ rewrite <- seq_concat_len s1 s2. rewrite Hlen1. exact Heq_len. }
rewrite Hn1_eq at 2. exact Hlt_cat.
Qed.

Theorem forms_valid_implies_safe_data : forall s, FormsValid s ->
  FormsBalanced s /\ QuoteFree s /\ 0 < seq_len s.
let s. assume Hv.
apply Hv. assume Hv1 Hs. apply Hv1. assume Hv2 Hqf. apply Hv2. assume Hv3 _. apply Hv3. assume Hpos _.
apply Hs. assume Hb _.
exact and3I (FormsBalanced s) (QuoteFree s) (0 < seq_len s) Hb Hqf Hpos.
Qed.

(** ---- Part 4: Streaming Transcript Tail Buffer Bound & Chunk Invariance --- *)

Definition TRANSCRIPT_LINES : set := 6.

Definition keep_last : set -> set -> set :=
  fun K s => if K <= seq_len s then seq_drop (seq_len s + - K) s else s.

Definition buf_feed : set -> set -> set -> set :=
  fun K b chunk => keep_last K (seq_concat b chunk).

Theorem keep_last_IsSeq : forall K :e omega, forall s, IsSeq s -> IsSeq (keep_last K s).
let K. assume HK. let s. assume Hs.
apply Hs. assume Hsn _.
apply xm (K <= seq_len s).
- assume Hge : K <= seq_len s.
  prove IsSeq (if K <= seq_len s then seq_drop (seq_len s + - K) s else s).
  rewrite If_i_1 (K <= seq_len s) (seq_drop (seq_len s + - K) s) s Hge.
  claim Hsub : seq_len s + - (seq_len s + - K) = K.
  { rewrite minus_add_SNo_distr (seq_len s) (- K) (omega_SNo (seq_len s) Hsn) (SNo_minus_SNo K (omega_SNo K HK)).
    rewrite minus_SNo_invol K (omega_SNo K HK).
    exact add_SNo_minus_L2' (seq_len s) K (omega_SNo (seq_len s) Hsn) (omega_SNo K HK). }
  prove IsSeq (Seq (seq_len s + - (seq_len s + - K)) (fun i => seq_at s ((seq_len s + - K) + i))).
  rewrite Hsub.
  exact IsSeq_mk K HK (fun i => seq_at s ((seq_len s + - K) + i)).
- assume Hnge : ~(K <= seq_len s).
  prove IsSeq (if K <= seq_len s then seq_drop (seq_len s + - K) s else s).
  rewrite If_i_0 (K <= seq_len s) (seq_drop (seq_len s + - K) s) s Hnge.
  exact Hs.
Qed.

Theorem keep_last_bounded : forall K :e omega, forall s, IsSeq s ->
  seq_len (keep_last K s) <= K /\ seq_len (keep_last K s) <= seq_len s.
let K. assume HK. let s. assume Hs.
apply Hs. assume Hsn _.
apply xm (K <= seq_len s).
- assume Hge : K <= seq_len s.
  claim Hlen : seq_len (keep_last K s) = K.
  { prove seq_len (if K <= seq_len s then seq_drop (seq_len s + - K) s else s) = K.
    rewrite If_i_1 (K <= seq_len s) (seq_drop (seq_len s + - K) s) s Hge.
    prove seq_len (Seq (seq_len s + - (seq_len s + - K)) (fun i => seq_at s ((seq_len s + - K) + i))) = K.
    rewrite seq_len_mk (seq_len s + - (seq_len s + - K)) (fun i => seq_at s ((seq_len s + - K) + i)).
    rewrite minus_add_SNo_distr (seq_len s) (- K) (omega_SNo (seq_len s) Hsn) (SNo_minus_SNo K (omega_SNo K HK)).
    rewrite minus_SNo_invol K (omega_SNo K HK).
    exact add_SNo_minus_L2' (seq_len s) K (omega_SNo (seq_len s) Hsn) (omega_SNo K HK). }
  rewrite Hlen.
  exact andI (K <= K) (K <= seq_len s) (SNoLe_ref K) Hge.
- assume Hnge : ~(K <= seq_len s).
  claim Heq : keep_last K s = s.
  { exact If_i_0 (K <= seq_len s) (seq_drop (seq_len s + - K) s) s Hnge. }
  rewrite Heq.
  apply andI.
  + apply nat_Le_or_Lt (seq_len s) Hsn K HK.
    * assume H : seq_len s <= K. exact H.
    * assume H : K < seq_len s. apply FalseE. exact Hnge (SNoLtLe K (seq_len s) H).
  + exact SNoLe_ref (seq_len s).
Qed.

Theorem keep_last_concat_drop : forall K :e omega, forall b c, IsSeq b -> IsSeq c ->
  keep_last K (seq_concat (keep_last K b) c) = keep_last K (seq_concat b c).
let K. assume HK. let b c. assume Hb Hc.
apply Hb. assume Hbn _. apply Hc. assume Hcn _.
apply xm (K <= seq_len b).
- assume Hge : K <= seq_len b.
  claim Hkb_eq : keep_last K b = seq_drop (seq_len b + - K) b.
  { exact If_i_1 (K <= seq_len b) (seq_drop (seq_len b + - K) b) b Hge. }
  claim Hkb_s : IsSeq (keep_last K b). { exact keep_last_IsSeq K HK b Hb. }
  claim Hkb_len : seq_len (keep_last K b) = K.
  { rewrite Hkb_eq.
    prove seq_len (Seq (seq_len b + - (seq_len b + - K)) (fun i => seq_at b ((seq_len b + - K) + i))) = K.
    rewrite seq_len_mk (seq_len b + - (seq_len b + - K)) (fun i => seq_at b ((seq_len b + - K) + i)).
    rewrite minus_add_SNo_distr (seq_len b) (- K) (omega_SNo (seq_len b) Hbn) (SNo_minus_SNo K (omega_SNo K HK)).
    rewrite minus_SNo_invol K (omega_SNo K HK).
    exact add_SNo_minus_L2' (seq_len b) K (omega_SNo (seq_len b) Hbn) (omega_SNo K HK). }
  claim Hkb_c : IsSeq (seq_concat (keep_last K b) c). { exact seq_concat_IsSeq (keep_last K b) c Hkb_s Hc. }
  claim Hbc : IsSeq (seq_concat b c). { exact seq_concat_IsSeq b c Hb Hc. }
  claim Hge1 : K <= seq_len (seq_concat (keep_last K b) c).
  { rewrite seq_concat_len (keep_last K b) c. rewrite Hkb_len.
    rewrite <- add_SNo_0R K (omega_SNo K HK) at 1.
    exact add_SNo_Le2 K 0 (seq_len c) (omega_SNo K HK) SNo_0 (omega_SNo (seq_len c) Hcn) (nat_0_Le (seq_len c) Hcn). }
  claim Hge2 : K <= seq_len (seq_concat b c).
  { rewrite seq_concat_len b c.
    apply SNoLe_tra K (seq_len b) (seq_len b + seq_len c) (omega_SNo K HK) (omega_SNo (seq_len b) Hbn)
          (omega_SNo (seq_len b + seq_len c) (nat_add_omega (seq_len b) Hbn (seq_len c) Hcn)) Hge.
    rewrite <- add_SNo_0R (seq_len b) (omega_SNo (seq_len b) Hbn) at 1.
    exact add_SNo_Le2 (seq_len b) 0 (seq_len c) (omega_SNo (seq_len b) Hbn) SNo_0 (omega_SNo (seq_len c) Hcn) (nat_0_Le (seq_len c) Hcn). }
  claim HL_eq : keep_last K (seq_concat (keep_last K b) c) = seq_drop (seq_len (seq_concat (keep_last K b) c) + - K) (seq_concat (keep_last K b) c).
  { exact If_i_1 (K <= seq_len (seq_concat (keep_last K b) c)) (seq_drop (seq_len (seq_concat (keep_last K b) c) + - K) (seq_concat (keep_last K b) c)) (seq_concat (keep_last K b) c) Hge1. }
  claim HR_eq : keep_last K (seq_concat b c) = seq_drop (seq_len (seq_concat b c) + - K) (seq_concat b c).
  { exact If_i_1 (K <= seq_len (seq_concat b c)) (seq_drop (seq_len (seq_concat b c) + - K) (seq_concat b c)) (seq_concat b c) Hge2. }
  claim HlenL : seq_len (keep_last K (seq_concat (keep_last K b) c)) = K.
  { rewrite HL_eq.
    prove seq_len (Seq (seq_len (seq_concat (keep_last K b) c) + - (seq_len (seq_concat (keep_last K b) c) + - K))
                       (fun i => seq_at (seq_concat (keep_last K b) c) ((seq_len (seq_concat (keep_last K b) c) + - K) + i))) = K.
    rewrite seq_len_mk (seq_len (seq_concat (keep_last K b) c) + - (seq_len (seq_concat (keep_last K b) c) + - K))
            (fun i => seq_at (seq_concat (keep_last K b) c) ((seq_len (seq_concat (keep_last K b) c) + - K) + i)).
    claim Hno : seq_len (seq_concat (keep_last K b) c) :e omega. { exact andEL (seq_len (seq_concat (keep_last K b) c) :e omega) (seq_concat (keep_last K b) c = Seq (seq_len (seq_concat (keep_last K b) c)) (fun j => seq_at (seq_concat (keep_last K b) c) j)) Hkb_c. }
    rewrite minus_add_SNo_distr (seq_len (seq_concat (keep_last K b) c)) (- K) (omega_SNo (seq_len (seq_concat (keep_last K b) c)) Hno) (SNo_minus_SNo K (omega_SNo K HK)).
    rewrite minus_SNo_invol K (omega_SNo K HK).
    exact add_SNo_minus_L2' (seq_len (seq_concat (keep_last K b) c)) K (omega_SNo (seq_len (seq_concat (keep_last K b) c)) Hno) (omega_SNo K HK). }
  claim HlenR : seq_len (keep_last K (seq_concat b c)) = K.
  { rewrite HR_eq.
    prove seq_len (Seq (seq_len (seq_concat b c) + - (seq_len (seq_concat b c) + - K))
                       (fun i => seq_at (seq_concat b c) ((seq_len (seq_concat b c) + - K) + i))) = K.
    rewrite seq_len_mk (seq_len (seq_concat b c) + - (seq_len (seq_concat b c) + - K))
            (fun i => seq_at (seq_concat b c) ((seq_len (seq_concat b c) + - K) + i)).
    claim Hno : seq_len (seq_concat b c) :e omega. { exact andEL (seq_len (seq_concat b c) :e omega) (seq_concat b c = Seq (seq_len (seq_concat b c)) (fun j => seq_at (seq_concat b c) j)) Hbc. }
    rewrite minus_add_SNo_distr (seq_len (seq_concat b c)) (- K) (omega_SNo (seq_len (seq_concat b c)) Hno) (SNo_minus_SNo K (omega_SNo K HK)).
    rewrite minus_SNo_invol K (omega_SNo K HK).
    exact add_SNo_minus_L2' (seq_len (seq_concat b c)) K (omega_SNo (seq_len (seq_concat b c)) Hno) (omega_SNo K HK). }
  apply seq_ext (keep_last K (seq_concat (keep_last K b) c)) (keep_last K (seq_concat b c))
        (keep_last_IsSeq K HK (seq_concat (keep_last K b) c) Hkb_c)
        (keep_last_IsSeq K HK (seq_concat b c) Hbc).
  + rewrite HlenL. rewrite HlenR. reflexivity.
  + let i. assume Hi.
    claim HiK : i :e K. { rewrite <- HlenL. exact Hi. }
    claim Hio : i :e omega. { exact nat_In_omega K HK i HiK. }
    claim Hd1 : seq_len (seq_concat (keep_last K b) c) + - K = seq_len c.
    { rewrite seq_concat_len (keep_last K b) c. rewrite Hkb_len.
      rewrite add_SNo_com K (seq_len c) (omega_SNo K HK) (omega_SNo (seq_len c) Hcn).
      exact add_SNo_minus_R2 (seq_len c) K (omega_SNo (seq_len c) Hcn) (omega_SNo K HK). }
    claim HbmK : seq_len b + - K :e omega. { exact nat_sub_omega K HK (seq_len b) Hbn Hge. }
    claim Hd2 : seq_len (seq_concat b c) + - K = (seq_len b + - K) + seq_len c.
    { rewrite seq_concat_len b c.
      rewrite add_SNo_com (seq_len b) (seq_len c) (omega_SNo (seq_len b) Hbn) (omega_SNo (seq_len c) Hcn).
      rewrite add_SNo_com (seq_len b + - K) (seq_len c) (omega_SNo (seq_len b + - K) HbmK) (omega_SNo (seq_len c) Hcn).
      symmetry. exact add_SNo_assoc (seq_len c) (seq_len b) (- K) (omega_SNo (seq_len c) Hcn) (omega_SNo (seq_len b) Hbn) (SNo_minus_SNo K (omega_SNo K HK)). }
    claim HatL : seq_at (keep_last K (seq_concat (keep_last K b) c)) i = seq_at (seq_concat (keep_last K b) c) (seq_len c + i).
    { rewrite HL_eq.
      claim Hno1 : seq_len (seq_concat (keep_last K b) c) :e omega.
      { exact andEL (seq_len (seq_concat (keep_last K b) c) :e omega) (seq_concat (keep_last K b) c = Seq (seq_len (seq_concat (keep_last K b) c)) (fun j => seq_at (seq_concat (keep_last K b) c) j)) Hkb_c. }
      claim Hi_sub : i :e seq_len (seq_concat (keep_last K b) c) + - (seq_len (seq_concat (keep_last K b) c) + - K).
      { rewrite SNo_sub_sub (seq_len (seq_concat (keep_last K b) c)) K (omega_SNo (seq_len (seq_concat (keep_last K b) c)) Hno1) (omega_SNo K HK).
        exact HiK. }
      prove seq_at (Seq (seq_len (seq_concat (keep_last K b) c) + - (seq_len (seq_concat (keep_last K b) c) + - K))
                        (fun j => seq_at (seq_concat (keep_last K b) c) ((seq_len (seq_concat (keep_last K b) c) + - K) + j))) i
          = seq_at (seq_concat (keep_last K b) c) (seq_len c + i).
      rewrite seq_at_mk (seq_len (seq_concat (keep_last K b) c) + - (seq_len (seq_concat (keep_last K b) c) + - K))
              (fun j => seq_at (seq_concat (keep_last K b) c) ((seq_len (seq_concat (keep_last K b) c) + - K) + j)) i Hi_sub.
      rewrite Hd1. reflexivity. }
    claim HatR : seq_at (keep_last K (seq_concat b c)) i = seq_at (seq_concat b c) (((seq_len b + - K) + seq_len c) + i).
    { rewrite HR_eq.
      claim Hno2 : seq_len (seq_concat b c) :e omega.
      { exact andEL (seq_len (seq_concat b c) :e omega) (seq_concat b c = Seq (seq_len (seq_concat b c)) (fun j => seq_at (seq_concat b c) j)) Hbc. }
      claim Hi_sub : i :e seq_len (seq_concat b c) + - (seq_len (seq_concat b c) + - K).
      { rewrite SNo_sub_sub (seq_len (seq_concat b c)) K (omega_SNo (seq_len (seq_concat b c)) Hno2) (omega_SNo K HK).
        exact HiK. }
      prove seq_at (Seq (seq_len (seq_concat b c) + - (seq_len (seq_concat b c) + - K))
                        (fun j => seq_at (seq_concat b c) ((seq_len (seq_concat b c) + - K) + j))) i
          = seq_at (seq_concat b c) (((seq_len b + - K) + seq_len c) + i).
      rewrite seq_at_mk (seq_len (seq_concat b c) + - (seq_len (seq_concat b c) + - K))
              (fun j => seq_at (seq_concat b c) ((seq_len (seq_concat b c) + - K) + j)) i Hi_sub.
      rewrite Hd2. reflexivity. }
    rewrite HatL. rewrite HatR.
    apply nat_Le_or_Lt K HK (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio).
    * assume Hci_ge : K <= seq_len c + i.
      claim Hq_o : (seq_len c + i) + - K :e omega.
      { exact nat_sub_omega K HK (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio) Hci_ge. }
      claim Hq_in_c : (seq_len c + i) + - K :e seq_len c.
      { apply nat_SNoLt_In (seq_len c) Hcn ((seq_len c + i) + - K) Hq_o.
        apply SNo_add_Lt_cancel_L K ((seq_len c + i) + - K) (seq_len c) (omega_SNo K HK) (omega_SNo ((seq_len c + i) + - K) Hq_o) (omega_SNo (seq_len c) Hcn).
        rewrite SNo_add_sub_L (seq_len c + i) K (omega_SNo (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio)) (omega_SNo K HK).
        rewrite add_SNo_com K (seq_len c) (omega_SNo K HK) (omega_SNo (seq_len c) Hcn).
        exact add_SNo_Lt2 (seq_len c) i K (omega_SNo (seq_len c) Hcn) (omega_SNo i Hio) (omega_SNo K HK) (nat_In_SNoLt K HK i HiK). }
      claim HeqL : seq_len c + i = seq_len (keep_last K b) + ((seq_len c + i) + - K).
      { rewrite Hkb_len. symmetry. exact SNo_add_sub_L (seq_len c + i) K (omega_SNo (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio)) (omega_SNo K HK). }
      claim HeqR : ((seq_len b + - K) + seq_len c) + i = seq_len b + ((seq_len c + i) + - K).
      { rewrite <- add_SNo_assoc (seq_len b + - K) (seq_len c) i (omega_SNo (seq_len b + - K) HbmK) (omega_SNo (seq_len c) Hcn) (omega_SNo i Hio).
        rewrite add_SNo_com (seq_len b) (- K) (omega_SNo (seq_len b) Hbn) (SNo_minus_SNo K (omega_SNo K HK)).
        rewrite <- add_SNo_assoc (- K) (seq_len b) (seq_len c + i) (SNo_minus_SNo K (omega_SNo K HK)) (omega_SNo (seq_len b) Hbn) (omega_SNo (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio)).
        rewrite add_SNo_com (- K) (seq_len b + (seq_len c + i)) (SNo_minus_SNo K (omega_SNo K HK)) (SNo_add_SNo (seq_len b) (seq_len c + i) (omega_SNo (seq_len b) Hbn) (omega_SNo (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio))).
        symmetry. exact add_SNo_assoc (seq_len b) (seq_len c + i) (- K) (omega_SNo (seq_len b) Hbn) (omega_SNo (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio)) (SNo_minus_SNo K (omega_SNo K HK)). }
      rewrite HeqL.
      rewrite seq_concat_at_R (keep_last K b) c Hkb_s Hc ((seq_len c + i) + - K) Hq_in_c.
      rewrite HeqR.
      rewrite seq_concat_at_R b c Hb Hc ((seq_len c + i) + - K) Hq_in_c.
      reflexivity.
    * assume Hci_lt : seq_len c + i < K.
      claim Hci_in_K : seq_len c + i :e K. { exact nat_SNoLt_In K HK (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio) Hci_lt. }
      claim Hci_in_kb : seq_len c + i :e seq_len (keep_last K b). { rewrite Hkb_len. exact Hci_in_K. }
      claim HidxR_eq : ((seq_len b + - K) + seq_len c) + i = (seq_len b + - K) + (seq_len c + i).
      { symmetry. exact add_SNo_assoc (seq_len b + - K) (seq_len c) i (omega_SNo (seq_len b + - K) HbmK) (omega_SNo (seq_len c) Hcn) (omega_SNo i Hio). }
      claim HidxR_in_b : (seq_len b + - K) + (seq_len c + i) :e seq_len b.
      { apply nat_SNoLt_In (seq_len b) Hbn ((seq_len b + - K) + (seq_len c + i)) (nat_add_omega (seq_len b + - K) HbmK (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio)).
        claim Hsub_K : (seq_len b + - K) + K = seq_len b.
        { rewrite add_SNo_com (seq_len b + - K) K (omega_SNo (seq_len b + - K) HbmK) (omega_SNo K HK).
          exact SNo_add_sub_L (seq_len b) K (omega_SNo (seq_len b) Hbn) (omega_SNo K HK). }
        rewrite <- Hsub_K at 2.
        exact add_SNo_Lt2 (seq_len b + - K) (seq_len c + i) K (omega_SNo (seq_len b + - K) HbmK)
              (omega_SNo (seq_len c + i) (nat_add_omega (seq_len c) Hcn i Hio)) (omega_SNo K HK) Hci_lt. }
      rewrite seq_concat_at_L (keep_last K b) c Hkb_s Hc (seq_len c + i) Hci_in_kb.
      rewrite HidxR_eq.
      rewrite seq_concat_at_L b c Hb Hc ((seq_len b + - K) + (seq_len c + i)) HidxR_in_b.
      rewrite Hkb_eq.
      claim Hci_in_sub : seq_len c + i :e seq_len b + - (seq_len b + - K).
      { rewrite SNo_sub_sub (seq_len b) K (omega_SNo (seq_len b) Hbn) (omega_SNo K HK).
        exact Hci_in_K. }
      exact seq_at_mk (seq_len b + - (seq_len b + - K)) (fun j => seq_at b ((seq_len b + - K) + j)) (seq_len c + i) Hci_in_sub.
- assume Hnge : ~(K <= seq_len b).
  claim Hkb_eq : keep_last K b = b. { exact If_i_0 (K <= seq_len b) (seq_drop (seq_len b + - K) b) b Hnge. }
  rewrite Hkb_eq. reflexivity.
Qed.

(** STREAMING CHUNK-INVARIANCE THEOREM (append_last_transcript_lines.metta:7-11):
    Reading any transcript split across arbitrary chunk boundaries c1, c2
    produces the exact same last-K line buffer as reading c1 ++ c2 in one shot! *)
Theorem transcript_tail_chunk_invariance : forall K :e omega, forall b c1 c2,
  IsSeq b -> IsSeq c1 -> IsSeq c2 ->
  buf_feed K (buf_feed K b c1) c2 = buf_feed K b (seq_concat c1 c2).
let K. assume HK. let b c1 c2. assume Hb Hc1 Hc2.
prove keep_last K (seq_concat (keep_last K (seq_concat b c1)) c2)
    = keep_last K (seq_concat b (seq_concat c1 c2)).
rewrite keep_last_concat_drop K HK (seq_concat b c1) c2 (seq_concat_IsSeq b c1 Hb Hc1) Hc2.
rewrite seq_concat_assoc b c1 c2 Hb Hc1 Hc2.
reflexivity.
Qed.

(** ---- Part 5: alarms.metta Due/Future Partition & Sorted Merge Invariants -- *)

Definition AlarmDue : set -> set -> prop := fun t now => t <= now.
Definition AlarmFuture : set -> set -> prop := fun t now => now < t.

Theorem alarm_partition_exhaustive : forall t :e real, forall now :e real,
  AlarmDue t now \/ AlarmFuture t now.
let t. assume Ht. let now. assume Hnow.
apply SNoLt_trichotomy_or t now (real_SNo t Ht) (real_SNo now Hnow).
- assume Hor. apply Hor.
  + assume Hlt : t < now. exact orIL (t <= now) (now < t) (SNoLtLe t now Hlt).
  + assume Heq : t = now. apply orIL. rewrite Heq. exact SNoLe_ref now.
- assume Hgt : now < t. exact orIR (t <= now) (now < t) Hgt.
Qed.

Theorem alarm_partition_disjoint : forall t :e real, forall now :e real,
  ~(AlarmDue t now /\ AlarmFuture t now).
let t. assume Ht. let now. assume Hnow. assume H.
apply H. assume Hle Hlt.
exact SNoLt_irref now (SNoLtLe_tra now t now (real_SNo now Hnow) (real_SNo t Ht) (real_SNo now Hnow) Hlt Hle).
Qed.

Definition SortedStrict : set -> prop :=
  fun s =>
    (forall i :e seq_len s, seq_at s i :e real) /\
    (forall i :e seq_len s, forall j :e seq_len s, i < j -> seq_at s i < seq_at s j).

Theorem sorted_strict_distinct : forall s, IsSeq s -> SortedStrict s ->
  forall i :e seq_len s, forall j :e seq_len s, i <> j -> seq_at s i <> seq_at s j.
let s. assume Hs Hsort. apply Hs. assume Hsn _. apply Hsort. assume Hreal Hord.
let i. assume Hi. let j. assume Hj Hne Heq.
claim Hio : i :e omega. { exact nat_In_omega (seq_len s) Hsn i Hi. }
claim Hjo : j :e omega. { exact nat_In_omega (seq_len s) Hsn j Hj. }
apply ordinal_trichotomy_or_impred i j (nat_p_ordinal i (omega_nat_p i Hio)) (nat_p_ordinal j (omega_nat_p j Hjo)).
- assume Hij : i :e j.
  claim Hlt : seq_at s i < seq_at s j. { exact Hord i Hi j Hj (nat_In_SNoLt j Hjo i Hij). }
  apply SNoLt_irref (seq_at s i). rewrite Heq at 2. exact Hlt.
- assume Hij : i = j. exact Hne Hij.
- assume Hji : j :e i.
  claim Hlt : seq_at s j < seq_at s i. { exact Hord j Hj i Hi (nat_In_SNoLt i Hio j Hji). }
  apply SNoLt_irref (seq_at s j). rewrite <- Heq at 2. exact Hlt.
Qed.

Theorem sorted_strict_drop_preserves : forall s, IsSeq s -> SortedStrict s ->
  forall d :e omega, d <= seq_len s -> SortedStrict (seq_drop d s).
let s. assume Hs Hsort. apply Hs. assume Hsn _. apply Hsort. assume Hreal Hord.
let d. assume Hd Hdle.
claim Hsub_o : seq_len s + - d :e omega. { exact nat_sub_omega d Hd (seq_len s) Hsn Hdle. }
claim Hlen : seq_len (seq_drop d s) = seq_len s + - d.
{ exact seq_len_mk (seq_len s + - d) (fun i => seq_at s (d + i)). }
prove (forall i :e seq_len (seq_drop d s), seq_at (seq_drop d s) i :e real) /\
      (forall i :e seq_len (seq_drop d s), forall j :e seq_len (seq_drop d s), i < j -> seq_at (seq_drop d s) i < seq_at (seq_drop d s) j).
apply andI.
- let i. assume Hi.
  claim Hi' : i :e seq_len s + - d. { rewrite <- Hlen. exact Hi. }
  claim Hdi : d + i :e seq_len s. { exact nat_In_sub_add (seq_len s) Hsn d Hd Hdle i Hi'. }
  prove seq_at (Seq (seq_len s + - d) (fun u => seq_at s (d + u))) i :e real.
  rewrite seq_at_mk (seq_len s + - d) (fun u => seq_at s (d + u)) i Hi'.
  exact Hreal (d + i) Hdi.
- let i. assume Hi. let j. assume Hj Hij.
  claim Hi' : i :e seq_len s + - d. { rewrite <- Hlen. exact Hi. }
  claim Hj' : j :e seq_len s + - d. { rewrite <- Hlen. exact Hj. }
  claim Hio : i :e omega. { exact nat_In_omega (seq_len s + - d) Hsub_o i Hi'. }
  claim Hjo : j :e omega. { exact nat_In_omega (seq_len s + - d) Hsub_o j Hj'. }
  claim Hdi : d + i :e seq_len s. { exact nat_In_sub_add (seq_len s) Hsn d Hd Hdle i Hi'. }
  claim Hdj : d + j :e seq_len s. { exact nat_In_sub_add (seq_len s) Hsn d Hd Hdle j Hj'. }
  prove seq_at (Seq (seq_len s + - d) (fun u => seq_at s (d + u))) i
      < seq_at (Seq (seq_len s + - d) (fun u => seq_at s (d + u))) j.
  rewrite seq_at_mk (seq_len s + - d) (fun u => seq_at s (d + u)) i Hi'.
  rewrite seq_at_mk (seq_len s + - d) (fun u => seq_at s (d + u)) j Hj'.
  exact Hord (d + i) Hdi (d + j) Hdj (add_SNo_Lt2 d i j (omega_SNo d Hd) (omega_SNo i Hio) (omega_SNo j Hjo) Hij).
Qed.

Definition seq_cons : set -> set -> set :=
  fun x s => Seq (1 + seq_len s) (fun i => if i = 0 then x else seq_at s (i + - 1)).

Theorem sorted_strict_cons_min : forall x :e real, forall s, IsSeq s -> SortedStrict s ->
  (forall j :e seq_len s, x < seq_at s j) ->
  SortedStrict (seq_cons x s).
let x. assume Hx. let s. assume Hs Hsort Hmin.
apply Hs. assume Hsn _. apply Hsort. assume Hreal Hord.
claim Hlen : seq_len (seq_cons x s) = 1 + seq_len s.
{ exact seq_len_mk (1 + seq_len s) (fun i => if i = 0 then x else seq_at s (i + - 1)). }
claim H1n : 1 + seq_len s :e omega. { exact nat_add_omega 1 nat_1_omega (seq_len s) Hsn. }
prove (forall i :e seq_len (seq_cons x s), seq_at (seq_cons x s) i :e real) /\
      (forall i :e seq_len (seq_cons x s), forall j :e seq_len (seq_cons x s), i < j -> seq_at (seq_cons x s) i < seq_at (seq_cons x s) j).
apply andI.
- let i. assume Hi.
  claim Hi' : i :e 1 + seq_len s. { rewrite <- Hlen. exact Hi. }
  claim Hio : i :e omega. { exact nat_In_omega (1 + seq_len s) H1n i Hi'. }
  prove seq_at (Seq (1 + seq_len s) (fun u => if u = 0 then x else seq_at s (u + - 1))) i :e real.
  rewrite seq_at_mk (1 + seq_len s) (fun u => if u = 0 then x else seq_at s (u + - 1)) i Hi'.
  apply xm (i = 0).
  + assume H0 : i = 0.
    rewrite If_i_1 (i = 0) x (seq_at s (i + - 1)) H0. exact Hx.
  + assume Hne0 : i <> 0.
    rewrite If_i_0 (i = 0) x (seq_at s (i + - 1)) Hne0.
    claim Hpos : 0 < i.
    { apply nat_Le_or_Lt i Hio 0 nat_0_omega.
      - assume Hle0 : i <= 0. apply FalseE. apply Hne0.
        exact SNoLe_antisym i 0 (omega_SNo i Hio) SNo_0 Hle0 (nat_0_Le i Hio).
      - assume H : 0 < i. exact H. }
    claim H1le : 1 <= i. { rewrite <- add_SNo_0L 1 SNo_1. exact nat_SNoLt_S_Le 0 nat_0_omega i Hio Hpos. }
    claim Him1_o : i + - 1 :e omega. { exact nat_sub_omega 1 nat_1_omega i Hio H1le. }
    claim Him1_in : i + - 1 :e seq_len s.
    { apply nat_SNoLt_In (seq_len s) Hsn (i + - 1) Him1_o.
      apply SNo_add_Lt_cancel_L 1 (i + - 1) (seq_len s) SNo_1 (omega_SNo (i + - 1) Him1_o) (omega_SNo (seq_len s) Hsn).
      rewrite SNo_add_sub_L i 1 (omega_SNo i Hio) SNo_1.
      exact nat_In_SNoLt (1 + seq_len s) H1n i Hi'. }
    exact Hreal (i + - 1) Him1_in.
- let i. assume Hi. let j. assume Hj Hij.
  claim Hi' : i :e 1 + seq_len s. { rewrite <- Hlen. exact Hi. }
  claim Hj' : j :e 1 + seq_len s. { rewrite <- Hlen. exact Hj. }
  claim Hio : i :e omega. { exact nat_In_omega (1 + seq_len s) H1n i Hi'. }
  claim Hjo : j :e omega. { exact nat_In_omega (1 + seq_len s) H1n j Hj'. }
  claim Hjpos : 0 < j. { exact SNoLeLt_tra 0 i j SNo_0 (omega_SNo i Hio) (omega_SNo j Hjo) (nat_0_Le i Hio) Hij. }
  claim Hjne0 : j <> 0. { assume H0 : j = 0. apply SNoLt_irref 0. rewrite <- H0 at 2. exact Hjpos. }
  claim H1lej : 1 <= j. { rewrite <- add_SNo_0L 1 SNo_1. exact nat_SNoLt_S_Le 0 nat_0_omega j Hjo Hjpos. }
  claim Hjm1_o : j + - 1 :e omega. { exact nat_sub_omega 1 nat_1_omega j Hjo H1lej. }
  claim Hjm1_in : j + - 1 :e seq_len s.
  { apply nat_SNoLt_In (seq_len s) Hsn (j + - 1) Hjm1_o.
    apply SNo_add_Lt_cancel_L 1 (j + - 1) (seq_len s) SNo_1 (omega_SNo (j + - 1) Hjm1_o) (omega_SNo (seq_len s) Hsn).
    rewrite SNo_add_sub_L j 1 (omega_SNo j Hjo) SNo_1.
    exact nat_In_SNoLt (1 + seq_len s) H1n j Hj'. }
  prove seq_at (Seq (1 + seq_len s) (fun u => if u = 0 then x else seq_at s (u + - 1))) i
      < seq_at (Seq (1 + seq_len s) (fun u => if u = 0 then x else seq_at s (u + - 1))) j.
  rewrite seq_at_mk (1 + seq_len s) (fun u => if u = 0 then x else seq_at s (u + - 1)) i Hi'.
  rewrite seq_at_mk (1 + seq_len s) (fun u => if u = 0 then x else seq_at s (u + - 1)) j Hj'.
  rewrite If_i_0 (j = 0) x (seq_at s (j + - 1)) Hjne0.
  apply xm (i = 0).
  + assume Hi0 : i = 0.
    rewrite If_i_1 (i = 0) x (seq_at s (i + - 1)) Hi0.
    exact Hmin (j + - 1) Hjm1_in.
  + assume Hine0 : i <> 0.
    rewrite If_i_0 (i = 0) x (seq_at s (i + - 1)) Hine0.
    claim Hipos : 0 < i.
    { apply nat_Le_or_Lt i Hio 0 nat_0_omega.
      - assume Hle0 : i <= 0. apply FalseE. apply Hine0.
        exact SNoLe_antisym i 0 (omega_SNo i Hio) SNo_0 Hle0 (nat_0_Le i Hio).
      - assume H : 0 < i. exact H. }
    claim H1lei : 1 <= i. { rewrite <- add_SNo_0L 1 SNo_1. exact nat_SNoLt_S_Le 0 nat_0_omega i Hio Hipos. }
    claim Him1_o : i + - 1 :e omega. { exact nat_sub_omega 1 nat_1_omega i Hio H1lei. }
    claim Him1_in : i + - 1 :e seq_len s.
    { apply nat_SNoLt_In (seq_len s) Hsn (i + - 1) Him1_o.
      apply SNo_add_Lt_cancel_L 1 (i + - 1) (seq_len s) SNo_1 (omega_SNo (i + - 1) Him1_o) (omega_SNo (seq_len s) Hsn).
      rewrite SNo_add_sub_L i 1 (omega_SNo i Hio) SNo_1.
      exact nat_In_SNoLt (1 + seq_len s) H1n i Hi'. }
    claim Hsub_lt : i + - 1 < j + - 1.
    { exact add_SNo_Lt1 i (- 1) j (omega_SNo i Hio) (SNo_minus_SNo 1 SNo_1) (omega_SNo j Hjo) Hij. }
    exact Hord (i + - 1) Him1_in (j + - 1) Hjm1_in Hsub_lt.
Qed.

End IterDataBoundaries.
