(** ============================================================================
   Iter Native MeTTa Architecture Verification - Module 3
   Main Loop State Machine, Atomic Checkpoint Rollback, Bounded Autonomy &
   Liveness, and Subprocess Worker Kwarg / Wire Protocol Soundness
   Target sources:
     iter-native-release-20261028/iter.metta (lines 104-246)
     iter-native-release-20261028/iter_worker.metta (lines 31-135)
   Checked natively by CeTTa's Megalodon kernel against standard Egal preamble.mgs.
   Zero document axioms. Zero admitted. Zero aby.
   ============================================================================ *)

Section IterLoopStateMachine.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

(** ---- Part 1: Natural Arithmetic & Sequence Primitives -------------------- *)

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

Theorem nat_Le_or_Lt : forall a :e omega, forall b :e omega, a <= b \/ b < a.
let a. assume Ha. let b. assume Hb.
apply ordinal_trichotomy_or_impred a b (nat_p_ordinal a (omega_nat_p a Ha)) (nat_p_ordinal b (omega_nat_p b Hb)).
- assume H : a :e b. apply orIL. exact SNoLtLe a b (nat_In_SNoLt b Hb a H).
- assume H : a = b. apply orIL. rewrite H. exact SNoLe_ref b.
- assume H : b :e a. apply orIR. exact nat_In_SNoLt a Ha b H.
Qed.

Theorem nat_0_neq_1 : 0 <> 1.
assume Heq : 0 = 1.
apply SNoLt_irref 0. rewrite Heq at 2. exact SNoLt_0_1.
Qed.

(** ---- Part 2: Messages, Sequences, Push, Concat & Rollback Take ----------- *)

Definition RoleUser : set := 0.
Definition RoleSystem : set := 1.
Definition RoleAssistant : set := 2.
Definition RoleTool : set := 3.

Theorem RoleUser_neq_Tool : RoleUser <> RoleTool.
assume Heq : 0 = 3.
apply SNoLt_irref 0. rewrite Heq at 2.
exact nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 0 In_0_3.
Qed.

Theorem RoleAssistant_neq_Tool : RoleAssistant <> RoleTool.
assume Heq : 2 = 3.
apply SNoLt_irref 2. rewrite Heq at 2.
exact nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 2 In_2_3.
Qed.

Definition Msg : set -> set -> set := fun r c => setsum r c.
Definition msg_role : set -> set := fun m => proj0 m.
Definition msg_content : set -> set := fun m => proj1 m.

Theorem msg_role_pair : forall r c, msg_role (Msg r c) = r.
let r c. exact proj0_pair_eq r c.
Qed.

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
  { apply lam_ext n. let i. assume Hi.
    symmetry. exact seq_at_mk n f i Hi. }
  rewrite Hlam. reflexivity.
Qed.

Definition seq_take : set -> set -> set :=
  fun k s => Seq k (fun i => seq_at s i).

Definition seq_push : set -> set -> set :=
  fun s m => Seq (seq_len s + 1) (fun i => if i = seq_len s then m else seq_at s i).

Definition seq_concat : set -> set -> set :=
  fun s t => Seq (seq_len s + seq_len t)
    (fun i => if i < seq_len s then seq_at s i else seq_at t (i + - seq_len s)).

Definition ToolPaired : set -> prop :=
  fun s =>
    forall i :e seq_len s, msg_role (seq_at s i) = RoleTool ->
      0 < i /\ (exists k :e omega, i = k + 1 /\
        (msg_role (seq_at s k) = RoleAssistant \/ msg_role (seq_at s k) = RoleTool)).

Definition AllTools : set -> prop :=
  fun t => forall i :e seq_len t, msg_role (seq_at t i) = RoleTool.

Theorem seq_take_concat_cancel : forall s t, IsSeq s -> IsSeq t ->
  seq_take (seq_len s) (seq_concat s t) = s.
let s t. assume Hs Ht.
apply Hs. assume Hsn Hseq. apply Ht. assume Htn _.
claim Hle : seq_len s <= seq_len s + seq_len t.
{ rewrite <- add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hsn) at 1.
  exact add_SNo_Le2 (seq_len s) 0 (seq_len t) (omega_SNo (seq_len s) Hsn) SNo_0 (omega_SNo (seq_len t) Htn) (nat_0_Le (seq_len t) Htn). }
claim Hlam : (fun i :e seq_len s => seq_at (seq_concat s t) i) = (fun i :e seq_len s => seq_at s i).
{ apply lam_ext (seq_len s). let i. assume Hi.
  claim Hio : i :e omega. { exact nat_In_omega (seq_len s) Hsn i Hi. }
  claim Hilt : i < seq_len s. { exact nat_In_SNoLt (seq_len s) Hsn i Hi. }
  claim Hicat : i :e seq_len s + seq_len t.
  { exact nat_SNoLt_In (seq_len s + seq_len t) (nat_add_omega (seq_len s) Hsn (seq_len t) Htn) i Hio
          (SNoLtLe_tra i (seq_len s) (seq_len s + seq_len t) (omega_SNo i Hio) (omega_SNo (seq_len s) Hsn)
            (omega_SNo (seq_len s + seq_len t) (nat_add_omega (seq_len s) Hsn (seq_len t) Htn)) Hilt Hle). }
  prove seq_at (Seq (seq_len s + seq_len t) (fun j => if j < seq_len s then seq_at s j else seq_at t (j + - seq_len s))) i = seq_at s i.
  rewrite seq_at_mk (seq_len s + seq_len t) (fun j => if j < seq_len s then seq_at s j else seq_at t (j + - seq_len s)) i Hicat.
  exact If_i_1 (i < seq_len s) (seq_at s i) (seq_at t (i + - seq_len s)) Hilt. }
prove setsum (seq_len s) (fun i :e seq_len s => seq_at (seq_concat s t) i) = s.
rewrite Hlam. symmetry. exact Hseq.
Qed.

Theorem seq_push_non_tool_preserves_ToolPaired : forall s m, IsSeq s -> ToolPaired s ->
  msg_role m <> RoleTool -> ToolPaired (seq_push s m).
let s m. assume Hs Htp Hnt.
apply Hs. assume Hsn _.
let i. assume Hi Htool.
claim Hi1 : i :e seq_len s + 1. { rewrite <- seq_len_mk (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j). exact Hi. }
claim Hio : i :e omega. { exact nat_In_omega (seq_len s + 1) (nat_add_omega (seq_len s) Hsn 1 nat_1_omega) i Hi1. }
claim Hine : i <> seq_len s.
{ assume Heq : i = seq_len s.
  claim Hati : seq_at (seq_push s m) i = m.
  { prove seq_at (Seq (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j)) i = m.
    rewrite seq_at_mk (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j) i Hi1.
    exact If_i_1 (i = seq_len s) m (seq_at s i) Heq. }
  apply Hnt. rewrite <- Hati. exact Htool. }
claim Hin : i :e seq_len s.
{ claim Hord : i :e ordsucc (seq_len s). { rewrite ordsucc_eq_add_1 (seq_len s) Hsn. exact Hi1. }
  apply ordsuccE (seq_len s) i Hord.
  - assume H : i :e seq_len s. exact H.
  - assume H : i = seq_len s. apply FalseE. exact Hine H. }
claim Hati : seq_at (seq_push s m) i = seq_at s i.
{ prove seq_at (Seq (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j)) i = seq_at s i.
  rewrite seq_at_mk (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j) i Hi1.
  exact If_i_0 (i = seq_len s) m (seq_at s i) Hine. }
claim Htool_s : msg_role (seq_at s i) = RoleTool. { rewrite <- Hati. exact Htool. }
apply Htp i Hin Htool_s. assume Hpos Hex.
apply andI.
- exact Hpos.
- apply Hex. let k. assume Hk. apply Hk. assume Hko Hk2. apply Hk2. assume Hik Hor.
  claim Hkn : k :e seq_len s.
  { apply nat_SNoLt_In (seq_len s) Hsn k Hko.
    apply SNoLt_tra k i (seq_len s) (omega_SNo k Hko) (omega_SNo i Hio) (omega_SNo (seq_len s) Hsn).
    - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
      exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
    - exact nat_In_SNoLt (seq_len s) Hsn i Hin. }
  claim Hkne : k <> seq_len s.
  { assume Heq : k = seq_len s. apply SNoLt_irref (seq_len s).
    rewrite <- Heq at 1. exact nat_In_SNoLt (seq_len s) Hsn k Hkn. }
  claim Hk1 : k :e seq_len s + 1.
  { rewrite <- ordsucc_eq_add_1 (seq_len s) Hsn. exact ordsuccI1 (seq_len s) k Hkn. }
  claim Hatk : seq_at (seq_push s m) k = seq_at s k.
  { prove seq_at (Seq (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j)) k = seq_at s k.
    rewrite seq_at_mk (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j) k Hk1.
    exact If_i_0 (k = seq_len s) m (seq_at s k) Hkne. }
  witness k. apply andI.
  + exact Hko.
  + apply andI.
    * exact Hik.
    * rewrite Hatk. exact Hor.
Qed.

Theorem seq_append_tool_block_preserves_ToolPaired : forall s a tools,
  IsSeq s -> IsSeq tools -> ToolPaired s -> AllTools tools ->
  ToolPaired (seq_concat (seq_push s (Msg RoleAssistant a)) tools).
let s a tools. assume Hs Htools Htp Hall.
apply Hs. assume Hsn _. apply Htools. assume Htn _.
claim Hsa_seq : IsSeq (seq_push s (Msg RoleAssistant a)).
{ exact IsSeq_mk (seq_len s + 1) (nat_add_omega (seq_len s) Hsn 1 nat_1_omega)
        (fun j => if j = seq_len s then Msg RoleAssistant a else seq_at s j). }
claim Hsa_len : seq_len (seq_push s (Msg RoleAssistant a)) = seq_len s + 1.
{ exact seq_len_mk (seq_len s + 1) (fun j => if j = seq_len s then Msg RoleAssistant a else seq_at s j). }
claim Hsa_o : seq_len (seq_push s (Msg RoleAssistant a)) :e omega.
{ rewrite Hsa_len. exact nat_add_omega (seq_len s) Hsn 1 nat_1_omega. }
claim Hsa_tp : ToolPaired (seq_push s (Msg RoleAssistant a)).
{ apply seq_push_non_tool_preserves_ToolPaired s (Msg RoleAssistant a) Hs Htp.
  rewrite msg_role_pair RoleAssistant a. exact RoleAssistant_neq_Tool. }
let i. assume Hi Htool.
claim Hcat_len : seq_len (seq_concat (seq_push s (Msg RoleAssistant a)) tools)
               = seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools.
{ exact seq_len_mk (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
        (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                  else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a)))). }
claim Hi_in : i :e seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools.
{ rewrite <- Hcat_len. exact Hi. }
claim Hio : i :e omega.
{ exact nat_In_omega (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
        (nat_add_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o (seq_len tools) Htn) i Hi_in. }
apply nat_Le_or_Lt (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o i Hio.
- assume Hge : seq_len (seq_push s (Msg RoleAssistant a)) <= i.
  claim Hipos : 0 < i.
  { apply SNoLtLe_tra 0 (seq_len s + 1) i SNo_0 (SNo_add_SNo (seq_len s) 1 (omega_SNo (seq_len s) Hsn) SNo_1) (omega_SNo i Hio).
    - apply SNoLeLt_tra 0 (seq_len s) (seq_len s + 1) SNo_0 (omega_SNo (seq_len s) Hsn) (SNo_add_SNo (seq_len s) 1 (omega_SNo (seq_len s) Hsn) SNo_1) (nat_0_Le (seq_len s) Hsn).
      rewrite <- add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hsn) at 1.
      exact add_SNo_Lt2 (seq_len s) 0 1 (omega_SNo (seq_len s) Hsn) SNo_0 SNo_1 SNoLt_0_1.
    - rewrite <- Hsa_len. exact Hge. }
  apply nat_pos_pred i Hio Hipos. let k. assume Hk. apply Hk. assume Hko Hik.
  claim Hk_cat : k :e seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools.
  { apply nat_SNoLt_In (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
          (nat_add_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o (seq_len tools) Htn) k Hko.
    apply SNoLt_tra k i (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
          (omega_SNo k Hko) (omega_SNo i Hio)
          (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
            (nat_add_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o (seq_len tools) Htn)).
    - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
      exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
    - exact nat_In_SNoLt (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
            (nat_add_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o (seq_len tools) Htn) i Hi_in. }
  apply andI.
  + exact Hipos.
  + witness k. apply andI.
    * exact Hko.
    * apply andI.
      { exact Hik. }
      { apply nat_Le_or_Lt (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o k Hko.
        - assume Hkge : seq_len (seq_push s (Msg RoleAssistant a)) <= k.
          apply orIR.
          claim Hknlt : ~(k < seq_len (seq_push s (Msg RoleAssistant a))).
          { assume Hlt : k < seq_len (seq_push s (Msg RoleAssistant a)).
            exact SNoLt_irref k (SNoLtLe_tra k (seq_len (seq_push s (Msg RoleAssistant a))) k (omega_SNo k Hko) (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o) (omega_SNo k Hko) Hlt Hkge). }
          claim Hksub_o : k + - seq_len (seq_push s (Msg RoleAssistant a)) :e omega.
          { exact nat_sub_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o k Hko Hkge. }
          claim Hksub_in : k + - seq_len (seq_push s (Msg RoleAssistant a)) :e seq_len tools.
          { apply nat_SNoLt_In (seq_len tools) Htn (k + - seq_len (seq_push s (Msg RoleAssistant a))) Hksub_o.
            claim Hklt : k < seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools.
            { exact nat_In_SNoLt (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
                    (nat_add_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o (seq_len tools) Htn) k Hk_cat. }
            apply SNo_add_Lt_cancel_L (seq_len (seq_push s (Msg RoleAssistant a))) (k + - seq_len (seq_push s (Msg RoleAssistant a))) (seq_len tools)
                  (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o)
                  (omega_SNo (k + - seq_len (seq_push s (Msg RoleAssistant a))) Hksub_o)
                  (omega_SNo (seq_len tools) Htn).
            rewrite SNo_add_sub_L k (seq_len (seq_push s (Msg RoleAssistant a))) (omega_SNo k Hko) (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o).
            exact Hklt. }
          claim Hatk : seq_at (seq_concat (seq_push s (Msg RoleAssistant a)) tools) k = seq_at tools (k + - seq_len (seq_push s (Msg RoleAssistant a))).
          { prove seq_at (Seq (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
                              (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                                        else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a))))) k
                = seq_at tools (k + - seq_len (seq_push s (Msg RoleAssistant a))).
            rewrite seq_at_mk (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
                    (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                              else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a)))) k Hk_cat.
            exact If_i_0 (k < seq_len (seq_push s (Msg RoleAssistant a))) (seq_at (seq_push s (Msg RoleAssistant a)) k)
                  (seq_at tools (k + - seq_len (seq_push s (Msg RoleAssistant a)))) Hknlt. }
          rewrite Hatk. exact Hall (k + - seq_len (seq_push s (Msg RoleAssistant a))) Hksub_in.
        - assume Hklt : k < seq_len (seq_push s (Msg RoleAssistant a)).
          apply orIL.
          claim Hkeq : k = seq_len s.
          { claim Hle1 : k + 1 <= seq_len s + 1.
            { rewrite <- Hsa_len. exact nat_SNoLt_S_Le k Hko (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o Hklt. }
            claim Hle2 : seq_len s + 1 <= k + 1.
            { rewrite <- Hik. rewrite <- Hsa_len. exact Hge. }
            claim Heq1 : k + 1 = seq_len s + 1. { exact SNoLe_antisym (k + 1) (seq_len s + 1) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) (SNo_add_SNo (seq_len s) 1 (omega_SNo (seq_len s) Hsn) SNo_1) Hle1 Hle2. }
            rewrite <- add_SNo_minus_R2 k 1 (omega_SNo k Hko) SNo_1.
            rewrite Heq1.
            exact add_SNo_minus_R2 (seq_len s) 1 (omega_SNo (seq_len s) Hsn) SNo_1. }
          claim Hk_in_sa : k :e seq_len s + 1.
          { rewrite <- Hsa_len. exact nat_SNoLt_In (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o k Hko Hklt. }
          claim Hatk : seq_at (seq_concat (seq_push s (Msg RoleAssistant a)) tools) k = seq_at (seq_push s (Msg RoleAssistant a)) k.
          { prove seq_at (Seq (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
                              (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                                        else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a))))) k
                = seq_at (seq_push s (Msg RoleAssistant a)) k.
            rewrite seq_at_mk (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
                    (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                              else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a)))) k Hk_cat.
            exact If_i_1 (k < seq_len (seq_push s (Msg RoleAssistant a))) (seq_at (seq_push s (Msg RoleAssistant a)) k)
                  (seq_at tools (k + - seq_len (seq_push s (Msg RoleAssistant a)))) Hklt. }
          claim Hata : seq_at (seq_push s (Msg RoleAssistant a)) k = Msg RoleAssistant a.
          { prove seq_at (Seq (seq_len s + 1) (fun j => if j = seq_len s then Msg RoleAssistant a else seq_at s j)) k = Msg RoleAssistant a.
            rewrite seq_at_mk (seq_len s + 1) (fun j => if j = seq_len s then Msg RoleAssistant a else seq_at s j) k Hk_in_sa.
            exact If_i_1 (k = seq_len s) (Msg RoleAssistant a) (seq_at s k) Hkeq. }
          rewrite Hatk. rewrite Hata. exact msg_role_pair RoleAssistant a. }
- assume Hilt : i < seq_len (seq_push s (Msg RoleAssistant a)).
  claim Hi_sa : i :e seq_len (seq_push s (Msg RoleAssistant a)).
  { exact nat_SNoLt_In (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o i Hio Hilt. }
  claim Hati : seq_at (seq_concat (seq_push s (Msg RoleAssistant a)) tools) i = seq_at (seq_push s (Msg RoleAssistant a)) i.
  { prove seq_at (Seq (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
                      (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                                else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a))))) i
        = seq_at (seq_push s (Msg RoleAssistant a)) i.
    rewrite seq_at_mk (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
            (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                      else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a)))) i Hi_in.
    exact If_i_1 (i < seq_len (seq_push s (Msg RoleAssistant a))) (seq_at (seq_push s (Msg RoleAssistant a)) i)
          (seq_at tools (i + - seq_len (seq_push s (Msg RoleAssistant a)))) Hilt. }
  claim Htool_sa : msg_role (seq_at (seq_push s (Msg RoleAssistant a)) i) = RoleTool.
  { rewrite <- Hati. exact Htool. }
  apply Hsa_tp i Hi_sa Htool_sa. assume Hpos Hex.
  apply andI.
  + exact Hpos.
  + apply Hex. let k. assume Hk. apply Hk. assume Hko Hk2. apply Hk2. assume Hik Hor.
    claim Hklt : k < seq_len (seq_push s (Msg RoleAssistant a)).
    { apply SNoLt_tra k i (seq_len (seq_push s (Msg RoleAssistant a))) (omega_SNo k Hko) (omega_SNo i Hio) (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o).
      - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
        exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
      - exact Hilt. }
    claim Hk_cat : k :e seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools.
    { apply nat_SNoLt_In (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
            (nat_add_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o (seq_len tools) Htn) k Hko.
      apply SNoLtLe_tra k (seq_len (seq_push s (Msg RoleAssistant a))) (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
            (omega_SNo k Hko) (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o)
            (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
              (nat_add_omega (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o (seq_len tools) Htn)) Hklt.
      rewrite <- add_SNo_0R (seq_len (seq_push s (Msg RoleAssistant a))) (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o) at 1.
      exact add_SNo_Le2 (seq_len (seq_push s (Msg RoleAssistant a))) 0 (seq_len tools)
            (omega_SNo (seq_len (seq_push s (Msg RoleAssistant a))) Hsa_o) SNo_0 (omega_SNo (seq_len tools) Htn) (nat_0_Le (seq_len tools) Htn). }
    claim Hatk : seq_at (seq_concat (seq_push s (Msg RoleAssistant a)) tools) k = seq_at (seq_push s (Msg RoleAssistant a)) k.
    { prove seq_at (Seq (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
                        (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                                  else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a))))) k
          = seq_at (seq_push s (Msg RoleAssistant a)) k.
      rewrite seq_at_mk (seq_len (seq_push s (Msg RoleAssistant a)) + seq_len tools)
              (fun j => if j < seq_len (seq_push s (Msg RoleAssistant a)) then seq_at (seq_push s (Msg RoleAssistant a)) j
                        else seq_at tools (j + - seq_len (seq_push s (Msg RoleAssistant a)))) k Hk_cat.
      exact If_i_1 (k < seq_len (seq_push s (Msg RoleAssistant a))) (seq_at (seq_push s (Msg RoleAssistant a)) k)
            (seq_at tools (k + - seq_len (seq_push s (Msg RoleAssistant a)))) Hklt. }
    witness k. apply andI.
    * exact Hko.
    * apply andI.
      { exact Hik. }
      { rewrite Hatk. exact Hor. }
Qed.

(** ---- Part 3: Three-Checkpoint Atomic Transaction & Peak Growth Bounds ---- *)

Theorem checkpoint_preserves_user_input : forall exp0 u partial,
  IsSeq exp0 -> ToolPaired exp0 -> IsSeq partial ->
  seq_take (seq_len (seq_push exp0 (Msg RoleUser u)))
           (seq_concat (seq_push exp0 (Msg RoleUser u)) partial)
  = seq_push exp0 (Msg RoleUser u)
  /\ ToolPaired (seq_push exp0 (Msg RoleUser u)).
let exp0 u partial. assume H0 Htp Hp.
apply H0. assume Hn0 _.
claim H1 : IsSeq (seq_push exp0 (Msg RoleUser u)).
{ exact IsSeq_mk (seq_len exp0 + 1) (nat_add_omega (seq_len exp0) Hn0 1 nat_1_omega)
        (fun i => if i = seq_len exp0 then Msg RoleUser u else seq_at exp0 i). }
apply andI.
- exact seq_take_concat_cancel (seq_push exp0 (Msg RoleUser u)) partial H1 Hp.
- apply seq_push_non_tool_preserves_ToolPaired exp0 (Msg RoleUser u) H0 Htp.
  rewrite msg_role_pair RoleUser u. exact RoleUser_neq_Tool.
Qed.

Theorem checkpoint_commits_atomic_tool_block : forall exp1 a tools trailing,
  IsSeq exp1 -> ToolPaired exp1 -> IsSeq tools -> AllTools tools -> IsSeq trailing ->
  seq_take (seq_len (seq_concat (seq_push exp1 (Msg RoleAssistant a)) tools))
           (seq_concat (seq_concat (seq_push exp1 (Msg RoleAssistant a)) tools) trailing)
  = seq_concat (seq_push exp1 (Msg RoleAssistant a)) tools
  /\ ToolPaired (seq_concat (seq_push exp1 (Msg RoleAssistant a)) tools).
let exp1 a tools trailing. assume H1 Htp1 Ht Hall Htr.
apply H1. assume Hn1 _. apply Ht. assume Hnt _.
claim H2 : IsSeq (seq_concat (seq_push exp1 (Msg RoleAssistant a)) tools).
{ claim Hsa_o : seq_len (seq_push exp1 (Msg RoleAssistant a)) :e omega.
  { prove seq_len (Seq (seq_len exp1 + 1) (fun j => if j = seq_len exp1 then Msg RoleAssistant a else seq_at exp1 j)) :e omega.
    rewrite seq_len_mk (seq_len exp1 + 1) (fun j => if j = seq_len exp1 then Msg RoleAssistant a else seq_at exp1 j).
    exact nat_add_omega (seq_len exp1) Hn1 1 nat_1_omega. }
  exact IsSeq_mk (seq_len (seq_push exp1 (Msg RoleAssistant a)) + seq_len tools)
        (nat_add_omega (seq_len (seq_push exp1 (Msg RoleAssistant a))) Hsa_o (seq_len tools) Hnt)
        (fun j => if j < seq_len (seq_push exp1 (Msg RoleAssistant a)) then seq_at (seq_push exp1 (Msg RoleAssistant a)) j
                  else seq_at tools (j + - seq_len (seq_push exp1 (Msg RoleAssistant a)))). }
apply andI.
- exact seq_take_concat_cancel (seq_concat (seq_push exp1 (Msg RoleAssistant a)) tools) trailing H2 Htr.
- exact seq_append_tool_block_preserves_ToolPaired exp1 a tools H1 Ht Htp1 Hall.
Qed.

Definition MAX_TOOL_CALLS : set := 10.
Definition MAX_STEP_GROWTH : set := 12.
Definition MAX_EXP_BOUND : set := 5 * (10 + 10).
Definition PEAK_EXP_BOUND : set := MAX_EXP_BOUND + 11.

Theorem n10_add_2_eq_12 : 1 + (1 + 10) = 12.
claim H10o : 10 :e omega. { exact nat_p_omega 10 nat_10. }
claim H11o : 11 :e omega. { exact nat_p_omega 11 nat_11. }
claim H11 : 1 + 10 = 11.
{ rewrite add_SNo_com 1 10 SNo_1 (omega_SNo 10 H10o).
  symmetry. exact ordsucc_eq_add_1 10 H10o. }
rewrite H11.
rewrite add_SNo_com 1 11 SNo_1 (omega_SNo 11 H11o).
symmetry. exact ordsucc_eq_add_1 11 H11o.
Qed.

Theorem step_growth_le_12 : forall n :e omega, forall u :e omega, forall k :e omega,
  u <= 1 -> k <= MAX_TOOL_CALLS ->
  n + (u + (1 + k)) <= n + MAX_STEP_GROWTH.
let n. assume Hn. let u. assume Hu. let k. assume Hk Hule Hkle.
claim H10o : 10 :e omega. { exact nat_p_omega 10 nat_10. }
claim H1k : 1 + k <= 1 + 10.
{ exact add_SNo_Le2 1 k 10 SNo_1 (omega_SNo k Hk) (omega_SNo 10 H10o) Hkle. }
claim Hu1k : u + (1 + k) <= 1 + (1 + 10).
{ exact add_SNo_Le3 u (1 + k) 1 (1 + 10) (omega_SNo u Hu) (omega_SNo (1 + k) (nat_add_omega 1 nat_1_omega k Hk))
        SNo_1 (omega_SNo (1 + 10) (nat_add_omega 1 nat_1_omega 10 H10o)) Hule H1k. }
prove n + (u + (1 + k)) <= n + 12.
rewrite <- n10_add_2_eq_12.
exact add_SNo_Le2 n (u + (1 + k)) (1 + (1 + 10)) (omega_SNo n Hn)
      (omega_SNo (u + (1 + k)) (nat_add_omega u Hu (1 + k) (nat_add_omega 1 nat_1_omega k Hk)))
      (omega_SNo (1 + (1 + 10)) (nat_add_omega 1 nat_1_omega (1 + 10) (nat_add_omega 1 nat_1_omega 10 H10o))) Hu1k.
Qed.

Theorem loop_peak_len_le_111 : forall n :e omega, forall u :e omega, forall k :e omega,
  n < MAX_EXP_BOUND -> u <= 1 -> k <= MAX_TOOL_CALLS ->
  n + (u + (1 + k)) <= PEAK_EXP_BOUND.
let n. assume Hn. let u. assume Hu. let k. assume Hk Hnlt Hule Hkle.
claim H100o : MAX_EXP_BOUND :e omega.
{ exact nat_mul_omega 5 (nat_p_omega 5 nat_5) (10 + 10) (nat_add_omega 10 (nat_p_omega 10 nat_10) 10 (nat_p_omega 10 nat_10)). }
claim H12o : 12 :e omega. { exact nat_p_omega 12 nat_12. }
claim H11o : 11 :e omega. { exact nat_p_omega 11 nat_11. }
claim Hn1_le : n + 1 <= MAX_EXP_BOUND. { exact nat_SNoLt_S_Le n Hn MAX_EXP_BOUND H100o Hnlt. }
claim H12_11 : 12 = 1 + 11.
{ rewrite add_SNo_com 1 11 SNo_1 (omega_SNo 11 H11o).
  exact ordsucc_eq_add_1 11 H11o. }
apply SNoLe_tra (n + (u + (1 + k))) (n + 12) (MAX_EXP_BOUND + 11)
      (omega_SNo (n + (u + (1 + k))) (nat_add_omega n Hn (u + (1 + k)) (nat_add_omega u Hu (1 + k) (nat_add_omega 1 nat_1_omega k Hk))))
      (omega_SNo (n + 12) (nat_add_omega n Hn 12 H12o))
      (omega_SNo (MAX_EXP_BOUND + 11) (nat_add_omega MAX_EXP_BOUND H100o 11 H11o)).
- exact step_growth_le_12 n Hn u Hu k Hk Hule Hkle.
- rewrite H12_11.
  rewrite add_SNo_assoc n 1 11 (omega_SNo n Hn) SNo_1 (omega_SNo 11 H11o).
  exact add_SNo_Le1 (n + 1) 11 MAX_EXP_BOUND (SNo_add_SNo n 1 (omega_SNo n Hn) SNo_1) (omega_SNo 11 H11o) (omega_SNo MAX_EXP_BOUND H100o) Hn1_le.
Qed.

(** ---- Part 4: Autonomy Invariant & Bounded Fast-Step Liveness (iter.metta:143-181) *)

Definition MAX_FAST_STEPS : set := 5 * 10.

Theorem n50_omega : MAX_FAST_STEPS :e omega.
exact nat_mul_omega 5 (nat_p_omega 5 nat_5) 10 (nat_p_omega 10 nat_10).
Qed.

Theorem n50_pos : 0 < MAX_FAST_STEPS.
exact mul_SNo_pos_pos 5 10 (omega_SNo 5 (nat_p_omega 5 nat_5)) (omega_SNo 10 (nat_p_omega 10 nat_10))
      (nat_In_SNoLt 5 (nat_p_omega 5 nat_5) 0 In_0_5)
      (nat_In_SNoLt 10 (nat_p_omega 10 nat_10) 0 (nat_0_in_ordsucc 9 nat_9)).
Qed.

(** Exact deterministic transition of Iter's autonomy/pacing state:
    Inputs: auto, new_burst, post_task, has_input (1 or 0), called_nop (1 or 0)
    Outputs: auto', new_burst', post_task', did_slow_wait *)
Definition next_auto : set -> set -> set -> set :=
  fun auto has_input called_nop =>
    if has_input = 1 then 0
    else if called_nop = 1 then 0
    else if MAX_FAST_STEPS <= auto + 1 then 0
    else auto + 1.

Definition next_new_burst : set -> set -> set :=
  fun has_input called_nop =>
    if has_input = 1 then 0
    else if called_nop = 1 then 1
    else 0.

Definition next_post_task : set -> set -> set -> set :=
  fun new_burst post_task has_input =>
    if has_input = 1 then 0
    else if new_burst = 1 then 1
    else post_task.

Definition did_slow_wait : set -> set -> set -> set :=
  fun auto has_input called_nop =>
    if has_input = 1 then 0
    else if called_nop = 1 then 1
    else if MAX_FAST_STEPS <= auto + 1 then 1
    else 0.

Theorem autonomy_invariant_lt_50 : forall auto :e omega, forall has_input called_nop,
  auto < MAX_FAST_STEPS ->
  next_auto auto has_input called_nop :e omega /\
  next_auto auto has_input called_nop < MAX_FAST_STEPS.
let auto. assume Ha. let has_input called_nop. assume Hlt.
apply xm (has_input = 1).
- assume Hin : has_input = 1.
  prove (if has_input = 1 then 0 else if called_nop = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) :e omega /\
        (if has_input = 1 then 0 else if called_nop = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) < MAX_FAST_STEPS.
  rewrite If_i_1 (has_input = 1) 0 (if called_nop = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) Hin.
  exact andI (0 :e omega) (0 < MAX_FAST_STEPS) nat_0_omega n50_pos.
- assume Hnin : has_input <> 1.
  prove (if has_input = 1 then 0 else if called_nop = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) :e omega /\
        (if has_input = 1 then 0 else if called_nop = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) < MAX_FAST_STEPS.
  rewrite If_i_0 (has_input = 1) 0 (if called_nop = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) Hnin.
  apply xm (called_nop = 1).
  + assume Hnop : called_nop = 1.
    rewrite If_i_1 (called_nop = 1) 0 (if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) Hnop.
    exact andI (0 :e omega) (0 < MAX_FAST_STEPS) nat_0_omega n50_pos.
  + assume Hnnop : called_nop <> 1.
    rewrite If_i_0 (called_nop = 1) 0 (if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) Hnnop.
    apply xm (MAX_FAST_STEPS <= auto + 1).
    * assume Hge : MAX_FAST_STEPS <= auto + 1.
      rewrite If_i_1 (MAX_FAST_STEPS <= auto + 1) 0 (auto + 1) Hge.
      exact andI (0 :e omega) (0 < MAX_FAST_STEPS) nat_0_omega n50_pos.
    * assume Hnge : ~(MAX_FAST_STEPS <= auto + 1).
      rewrite If_i_0 (MAX_FAST_STEPS <= auto + 1) 0 (auto + 1) Hnge.
      claim Ha1o : auto + 1 :e omega. { exact nat_add_omega auto Ha 1 nat_1_omega. }
      apply andI.
      { exact Ha1o. }
      { apply nat_Le_or_Lt MAX_FAST_STEPS n50_omega (auto + 1) Ha1o.
        - assume H : MAX_FAST_STEPS <= auto + 1. apply FalseE. exact Hnge H.
        - assume H : auto + 1 < MAX_FAST_STEPS. exact H. }
Qed.

Theorem user_input_resets_autonomy : forall auto nb pt called_nop,
  next_auto auto 1 called_nop = 0 /\
  next_new_burst 1 called_nop = 0 /\
  next_post_task nb pt 1 = 0 /\
  did_slow_wait auto 1 called_nop = 0.
let auto nb pt called_nop.
claim Href1 : 1 = 1. { reflexivity. }
apply andI.
- apply andI.
  + apply andI.
    * exact If_i_1 (1 = 1) 0 (if called_nop = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) Href1.
    * exact If_i_1 (1 = 1) 0 (if called_nop = 1 then 1 else 0) Href1.
  + exact If_i_1 (1 = 1) 0 (if nb = 1 then 1 else pt) Href1.
- exact If_i_1 (1 = 1) 0 (if called_nop = 1 then 1 else if MAX_FAST_STEPS <= auto + 1 then 1 else 0) Href1.
Qed.

Theorem nop_forces_slow_wait_and_burst : forall auto,
  next_auto auto 0 1 = 0 /\
  next_new_burst 0 1 = 1 /\
  did_slow_wait auto 0 1 = 1.
let auto.
claim Href1 : 1 = 1. { reflexivity. }
apply and3I.
- prove (if 0 = 1 then 0 else if 1 = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) = 0.
  rewrite If_i_0 (0 = 1) 0 (if 1 = 1 then 0 else if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) nat_0_neq_1.
  exact If_i_1 (1 = 1) 0 (if MAX_FAST_STEPS <= auto + 1 then 0 else auto + 1) Href1.
- prove (if 0 = 1 then 0 else if 1 = 1 then 1 else 0) = 1.
  rewrite If_i_0 (0 = 1) 0 (if 1 = 1 then 1 else 0) nat_0_neq_1.
  exact If_i_1 (1 = 1) 1 0 Href1.
- prove (if 0 = 1 then 0 else if 1 = 1 then 1 else if MAX_FAST_STEPS <= auto + 1 then 1 else 0) = 1.
  rewrite If_i_0 (0 = 1) 0 (if 1 = 1 then 1 else if MAX_FAST_STEPS <= auto + 1 then 1 else 0) nat_0_neq_1.
  exact If_i_1 (1 = 1) 1 (if MAX_FAST_STEPS <= auto + 1 then 1 else 0) Href1.
Qed.

(** Iterated autonomous non-nop steps starting from auto *)
Definition auto_run : set -> set -> set :=
  fun auto steps => nat_primrec auto (fun _ r => next_auto r 0 0) steps.

Theorem auto_run_0 : forall auto, auto_run auto 0 = auto.
let auto. exact nat_primrec_0 auto (fun _ r => next_auto r 0 0).
Qed.

Theorem auto_run_S : forall auto, forall k :e omega,
  auto_run auto (k + 1) = next_auto (auto_run auto k) 0 0.
let auto. let k. assume Hk.
rewrite <- ordsucc_eq_add_1 k Hk.
exact nat_primrec_S auto (fun _ r => next_auto r 0 0) k (omega_nat_p k Hk).
Qed.

Theorem auto_run_linear : forall k :e omega, forall auto :e omega,
  auto + k < MAX_FAST_STEPS -> auto_run auto k = auto + k.
let k. assume Hk.
apply nat_ind (fun m => forall auto :e omega, auto + m < MAX_FAST_STEPS -> auto_run auto m = auto + m).
- let auto. assume Ha _.
  rewrite auto_run_0 auto.
  symmetry. exact add_SNo_0R auto (omega_SNo auto Ha).
- let m. assume Hm IH.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  let auto. assume Ha Hlt.
  rewrite ordsucc_eq_add_1 m Hmo.
  rewrite auto_run_S auto m Hmo.
  claim Hltm : auto + m < MAX_FAST_STEPS.
  { apply SNoLt_tra (auto + m) (auto + (m + 1)) MAX_FAST_STEPS
          (omega_SNo (auto + m) (nat_add_omega auto Ha m Hmo))
          (omega_SNo (auto + (m + 1)) (nat_add_omega auto Ha (m + 1) (nat_add_omega m Hmo 1 nat_1_omega)))
          (omega_SNo MAX_FAST_STEPS n50_omega).
    - rewrite add_SNo_assoc auto m 1 (omega_SNo auto Ha) (omega_SNo m Hmo) SNo_1.
      rewrite <- add_SNo_0R (auto + m) (omega_SNo (auto + m) (nat_add_omega auto Ha m Hmo)) at 1.
      exact add_SNo_Lt2 (auto + m) 0 1 (omega_SNo (auto + m) (nat_add_omega auto Ha m Hmo)) SNo_0 SNo_1 SNoLt_0_1.
    - rewrite <- ordsucc_eq_add_1 m Hmo. exact Hlt. }
  rewrite IH auto Ha Hltm.
  claim Hlt_next : (auto + m) + 1 < MAX_FAST_STEPS.
  { rewrite <- add_SNo_assoc auto m 1 (omega_SNo auto Ha) (omega_SNo m Hmo) SNo_1.
    rewrite <- ordsucc_eq_add_1 m Hmo. exact Hlt. }
  claim Hnge : ~(MAX_FAST_STEPS <= (auto + m) + 1).
  { assume Hge : MAX_FAST_STEPS <= (auto + m) + 1.
    exact SNoLt_irref MAX_FAST_STEPS
          (SNoLeLt_tra MAX_FAST_STEPS ((auto + m) + 1) MAX_FAST_STEPS (omega_SNo MAX_FAST_STEPS n50_omega)
            (omega_SNo ((auto + m) + 1) (nat_add_omega (auto + m) (nat_add_omega auto Ha m Hmo) 1 nat_1_omega))
            (omega_SNo MAX_FAST_STEPS n50_omega) Hge Hlt_next). }
  prove (if 0 = 1 then 0 else if 0 = 1 then 0 else if MAX_FAST_STEPS <= (auto + m) + 1 then 0 else (auto + m) + 1) = auto + (m + 1).
  rewrite If_i_0 (0 = 1) 0 (if 0 = 1 then 0 else if MAX_FAST_STEPS <= (auto + m) + 1 then 0 else (auto + m) + 1) nat_0_neq_1.
  rewrite If_i_0 (0 = 1) 0 (if MAX_FAST_STEPS <= (auto + m) + 1 then 0 else (auto + m) + 1) nat_0_neq_1.
  rewrite If_i_0 (MAX_FAST_STEPS <= (auto + m) + 1) 0 ((auto + m) + 1) Hnge.
  symmetry. exact add_SNo_assoc auto m 1 (omega_SNo auto Ha) (omega_SNo m Hmo) SNo_1.
- exact omega_nat_p k Hk.
Qed.

(** BOUNDED FAST-LOOP LIVENESS THEOREM:
    From ANY valid auto < 50, after exactly k = (50 - auto) - 1 consecutive
    autonomous non-nop steps, the very next step MUST trigger slow_wait_for_input
    and reset auto back to 0! *)
Theorem bounded_fast_steps_liveness : forall auto :e omega, auto < MAX_FAST_STEPS ->
  exists k :e omega, k < MAX_FAST_STEPS /\
    did_slow_wait (auto_run auto k) 0 0 = 1 /\
    next_auto (auto_run auto k) 0 0 = 0.
let auto. assume Ha Hlt.
claim Hrem_pos : 0 < MAX_FAST_STEPS + - auto.
{ claim Hrem_o : MAX_FAST_STEPS + - auto :e omega.
  { exact nat_sub_omega auto Ha MAX_FAST_STEPS n50_omega (SNoLtLe auto MAX_FAST_STEPS Hlt). }
  apply nat_Le_or_Lt (MAX_FAST_STEPS + - auto) Hrem_o 0 nat_0_omega.
  - assume Hle0 : MAX_FAST_STEPS + - auto <= 0.
    apply FalseE.
    claim Hle50 : MAX_FAST_STEPS <= auto.
    { rewrite <- SNo_add_sub_L MAX_FAST_STEPS auto (omega_SNo MAX_FAST_STEPS n50_omega) (omega_SNo auto Ha).
      rewrite <- add_SNo_0R auto (omega_SNo auto Ha) at 3.
      exact add_SNo_Le2 auto (MAX_FAST_STEPS + - auto) 0 (omega_SNo auto Ha) (omega_SNo (MAX_FAST_STEPS + - auto) Hrem_o) SNo_0 Hle0. }
    exact SNoLt_irref auto (SNoLtLe_tra auto MAX_FAST_STEPS auto (omega_SNo auto Ha) (omega_SNo MAX_FAST_STEPS n50_omega) (omega_SNo auto Ha) Hlt Hle50).
  - assume Hpos : 0 < MAX_FAST_STEPS + - auto. exact Hpos. }
claim Hrem_o : MAX_FAST_STEPS + - auto :e omega.
{ exact nat_sub_omega auto Ha MAX_FAST_STEPS n50_omega (SNoLtLe auto MAX_FAST_STEPS Hlt). }
apply nat_pos_pred (MAX_FAST_STEPS + - auto) Hrem_o Hrem_pos.
let k. assume Hk. apply Hk. assume Hko Hkeq.
claim Hsum : (auto + k) + 1 = MAX_FAST_STEPS.
{ rewrite <- add_SNo_assoc auto k 1 (omega_SNo auto Ha) (omega_SNo k Hko) SNo_1.
  rewrite <- Hkeq.
  exact SNo_add_sub_L MAX_FAST_STEPS auto (omega_SNo MAX_FAST_STEPS n50_omega) (omega_SNo auto Ha). }
claim Hak_lt : auto + k < MAX_FAST_STEPS.
{ rewrite <- Hsum.
  rewrite <- add_SNo_0R (auto + k) (omega_SNo (auto + k) (nat_add_omega auto Ha k Hko)) at 1.
  exact add_SNo_Lt2 (auto + k) 0 1 (omega_SNo (auto + k) (nat_add_omega auto Ha k Hko)) SNo_0 SNo_1 SNoLt_0_1. }
claim Hk_lt : k < MAX_FAST_STEPS.
{ apply SNoLeLt_tra k (auto + k) MAX_FAST_STEPS (omega_SNo k Hko) (omega_SNo (auto + k) (nat_add_omega auto Ha k Hko)) (omega_SNo MAX_FAST_STEPS n50_omega).
  - rewrite <- add_SNo_0L k (omega_SNo k Hko) at 1.
    exact add_SNo_Le1 0 k auto SNo_0 (omega_SNo k Hko) (omega_SNo auto Ha) (nat_0_Le auto Ha).
  - exact Hak_lt. }
claim Hrun : auto_run auto k = auto + k. { exact auto_run_linear k Hko auto Ha Hak_lt. }
witness k. apply andI.
- exact Hko.
- apply and3I.
  + exact Hk_lt.
  + rewrite Hrun.
    prove (if 0 = 1 then 0 else if 0 = 1 then 1 else if MAX_FAST_STEPS <= (auto + k) + 1 then 1 else 0) = 1.
    rewrite If_i_0 (0 = 1) 0 (if 0 = 1 then 1 else if MAX_FAST_STEPS <= (auto + k) + 1 then 1 else 0) nat_0_neq_1.
    rewrite If_i_0 (0 = 1) 1 (if MAX_FAST_STEPS <= (auto + k) + 1 then 1 else 0) nat_0_neq_1.
    rewrite Hsum.
    exact If_i_1 (MAX_FAST_STEPS <= MAX_FAST_STEPS) 1 0 (SNoLe_ref MAX_FAST_STEPS).
  + rewrite Hrun.
    prove (if 0 = 1 then 0 else if 0 = 1 then 0 else if MAX_FAST_STEPS <= (auto + k) + 1 then 0 else (auto + k) + 1) = 0.
    rewrite If_i_0 (0 = 1) 0 (if 0 = 1 then 0 else if MAX_FAST_STEPS <= (auto + k) + 1 then 0 else (auto + k) + 1) nat_0_neq_1.
    rewrite If_i_0 (0 = 1) 0 (if MAX_FAST_STEPS <= (auto + k) + 1 then 0 else (auto + k) + 1) nat_0_neq_1.
    rewrite Hsum.
    exact If_i_1 (MAX_FAST_STEPS <= MAX_FAST_STEPS) 0 MAX_FAST_STEPS (SNoLe_ref MAX_FAST_STEPS).
Qed.

(** ---- Part 5: Worker Subprocess Protocol & Kwarg Soundness (iter_worker.metta) *)

Definition worker_missing : set -> set -> set -> set :=
  fun P D K => {p :e P | p /:e K /\ p /:e D}.

Definition worker_unexpected : set -> set -> set :=
  fun P K => {k :e K | k /:e P}.

Theorem worker_kwargs_sound : forall P D K,
  (worker_missing P D K = Empty /\ worker_unexpected P K = Empty) <->
  (P c= K :\/: D /\ K c= P).
let P D K.
apply iffI.
- assume H. apply H. assume Hmiss Hunexp.
  apply andI.
  + let p. assume Hp.
    apply xm (p :e K).
    * assume Hpk : p :e K. exact binunionI1 K D p Hpk.
    * assume Hnpk : p /:e K.
      apply xm (p :e D).
      { assume Hpd : p :e D. exact binunionI2 K D p Hpd. }
      { assume Hnpd : p /:e D. apply FalseE.
        claim Hpin : p :e worker_missing P D K.
        { exact SepI P (fun x => x /:e K /\ x /:e D) p Hp (andI (p /:e K) (p /:e D) Hnpk Hnpd). }
        claim Hpe : p :e Empty. { rewrite <- Hmiss. exact Hpin. }
        exact EmptyE p Hpe. }
  + let k. assume Hk.
    apply xm (k :e P).
    * assume Hkp : k :e P. exact Hkp.
    * assume Hnkp : k /:e P. apply FalseE.
      claim Hkin : k :e worker_unexpected P K.
      { exact SepI K (fun x => x /:e P) k Hk Hnkp. }
      claim Hke : k :e Empty. { rewrite <- Hunexp. exact Hkin. }
      exact EmptyE k Hke.
- assume H. apply H. assume Hsub1 Hsub2.
  apply andI.
  + apply set_ext.
    * let p. assume Hp.
      apply FalseE.
      claim HpP : p :e P. { exact SepE1 P (fun x => x /:e K /\ x /:e D) p Hp. }
      claim Hpn : p /:e K /\ p /:e D. { exact SepE2 P (fun x => x /:e K /\ x /:e D) p Hp. }
      apply Hpn. assume Hnpk Hnpd.
      apply binunionE K D p (Hsub1 p HpP).
      { assume Hpk : p :e K. exact Hnpk Hpk. }
      { assume Hpd : p :e D. exact Hnpd Hpd. }
    * let p. assume Hp. apply FalseE. exact EmptyE p Hp.
  + apply set_ext.
    * let k. assume Hk.
      apply FalseE.
      claim HkK : k :e K. { exact SepE1 K (fun x => x /:e P) k Hk. }
      claim Hnkp : k /:e P. { exact SepE2 K (fun x => x /:e P) k Hk. }
      exact Hnkp (Hsub2 k HkK).
    * let k. assume Hk. apply FalseE. exact EmptyE k Hk.
Qed.

Theorem worker_param_dispatch_total : forall P D K,
  worker_missing P D K = Empty -> worker_unexpected P K = Empty ->
  forall p :e P, p :e K \/ (p /:e K /\ p :e D).
let P D K. assume Hm Hu.
claim Hiff : P c= K :\/: D /\ K c= P.
{ exact iffEL (worker_missing P D K = Empty /\ worker_unexpected P K = Empty) (P c= K :\/: D /\ K c= P)
        (worker_kwargs_sound P D K) (andI (worker_missing P D K = Empty) (worker_unexpected P K = Empty) Hm Hu). }
apply Hiff. assume Hsub _.
let p. assume Hp.
apply xm (p :e K).
- assume Hpk : p :e K. exact orIL (p :e K) (p /:e K /\ p :e D) Hpk.
- assume Hnpk : p /:e K.
  apply orIR. apply andI.
  + exact Hnpk.
  + apply binunionE K D p (Hsub p Hp).
    * assume Hpk : p :e K. apply FalseE. exact Hnpk Hpk.
    * assume Hpd : p :e D. exact Hpd.
Qed.

Definition WireOk : set -> set := fun v => setsum 0 v.
Definition WireFail : set -> set := fun e => setsum 1 e.

Theorem worker_wire_disjoint : forall v e, WireOk v <> WireFail e.
let v e. assume Heq.
apply nat_0_neq_1.
claim H0 : proj0 (WireOk v) = 0. { exact proj0_pair_eq 0 v. }
claim H1 : proj0 (WireFail e) = 1. { exact proj0_pair_eq 1 e. }
rewrite <- H0 at 1. rewrite <- H1.
rewrite Heq. reflexivity.
Qed.

Theorem worker_wire_ok_inj : forall v1 v2, WireOk v1 = WireOk v2 -> v1 = v2.
let v1 v2. assume Heq.
claim H1 : proj1 (WireOk v1) = v1. { exact proj1_pair_eq 0 v1. }
claim H2 : proj1 (WireOk v2) = v2. { exact proj1_pair_eq 0 v2. }
rewrite <- H1. rewrite <- H2.
rewrite Heq. reflexivity.
Qed.

Theorem worker_wire_fail_inj : forall e1 e2, WireFail e1 = WireFail e2 -> e1 = e2.
let e1 e2. assume Heq.
claim H1 : proj1 (WireFail e1) = e1. { exact proj1_pair_eq 1 e1. }
claim H2 : proj1 (WireFail e2) = e2. { exact proj1_pair_eq 1 e2. }
rewrite <- H1. rewrite <- H2.
rewrite Heq. reflexivity.
Qed.

Definition trunc_len : set -> set -> set := fun L cap => if cap < L then cap else L.

Theorem tool_output_truncation_bound : forall L :e omega, forall cap :e omega,
  trunc_len L cap <= cap /\ trunc_len L cap <= L.
let L. assume HL. let cap. assume Hc.
apply xm (cap < L).
- assume Hlt : cap < L.
  prove (if cap < L then cap else L) <= cap /\ (if cap < L then cap else L) <= L.
  rewrite If_i_1 (cap < L) cap L Hlt.
  exact andI (cap <= cap) (cap <= L) (SNoLe_ref cap) (SNoLtLe cap L Hlt).
- assume Hnlt : ~(cap < L).
  prove (if cap < L then cap else L) <= cap /\ (if cap < L then cap else L) <= L.
  rewrite If_i_0 (cap < L) cap L Hnlt.
  apply andI.
  + apply nat_Le_or_Lt L HL cap Hc.
    * assume H : L <= cap. exact H.
    * assume H : cap < L. apply FalseE. exact Hnlt H.
  + exact SNoLe_ref L.
Qed.

End IterLoopStateMachine.
