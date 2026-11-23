(** ============================================================================
   Iter Native MeTTa Architecture Verification - Module 2
   Experience Hygiene, Windowing, Tool-Pairing Preservation, Multi-Step Cleanup
   Cadence Dichotomy, & Pure Stateless Experience Normalization
   Target source: iter-native-release-20261028/iter.metta (lines 67-127, 223-245)
   Checked natively by CeTTa's Megalodon kernel against standard Egal preamble.mgs.
   Zero document axioms. Zero admitted. Zero aby.
   ============================================================================ *)

Section IterExperienceHygiene.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

(** ---- Part 1: Natural Arithmetic & Ordering Bridge on omega --------------- *)

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
- assume Heq : m = n.
  apply FalseE. apply SNoLt_irref m.
  rewrite Heq at 2. exact Hlt.
- assume Hrev : n :e m.
  apply FalseE.
  claim Hgt : n < m. { exact nat_In_SNoLt m Hm n Hrev. }
  exact SNoLt_irref m (SNoLt_tra m n m (omega_SNo m Hm) (omega_SNo n Hn) (omega_SNo m Hm) Hlt Hgt).
Qed.

Theorem nat_SNoLe_cases : forall m :e omega, forall n :e omega, m <= n -> m :e n \/ m = n.
let m. assume Hm. let n. assume Hn. assume Hle.
apply ordinal_trichotomy_or_impred m n (nat_p_ordinal m (omega_nat_p m Hm)) (nat_p_ordinal n (omega_nat_p n Hn)).
- assume H : m :e n. exact orIL (m :e n) (m = n) H.
- assume H : m = n. exact orIR (m :e n) (m = n) H.
- assume Hrev : n :e m.
  apply FalseE.
  claim Hgt : n < m. { exact nat_In_SNoLt m Hm n Hrev. }
  exact SNoLt_irref n (SNoLtLe_tra n m n (omega_SNo n Hn) (omega_SNo m Hm) (omega_SNo n Hn) Hgt Hle).
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

Theorem nat_Le_In_ordsucc : forall m :e omega, forall n :e omega, m <= n -> m :e ordsucc n.
let m. assume Hm. let n. assume Hn. assume Hle.
apply nat_SNoLe_cases m Hm n Hn Hle.
- assume Hin : m :e n. exact ordsuccI1 n m Hin.
- assume Heq : m = n. rewrite Heq. exact ordsuccI2 n.
Qed.

Theorem nat_In_ordsucc_Le : forall n :e omega, forall m :e ordsucc n, m <= n.
let n. assume Hn. let m. assume Hm.
apply ordsuccE n m Hm.
- assume Hin : m :e n. exact SNoLtLe m n (nat_In_SNoLt n Hn m Hin).
- assume Heq : m = n. rewrite Heq. exact SNoLe_ref n.
Qed.

Theorem nat_In_omega : forall n :e omega, forall m :e n, m :e omega.
let n. assume Hn. let m. assume Hm.
exact nat_p_omega m (nat_p_trans n (omega_nat_p n Hn) m Hm).
Qed.

Theorem nat_pos_pred : forall n :e omega, 0 < n -> exists k :e omega, n = k + 1.
let n. assume Hn Hpos.
apply nat_inv n (omega_nat_p n Hn).
- assume H0 : n = 0.
  apply FalseE. apply SNoLt_irref 0.
  rewrite <- H0 at 2. exact Hpos.
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
claim Hmk : m :e ordsucc k.
{ rewrite ordsucc_eq_add_1 k Hko. rewrite <- Heq. exact Hin. }
claim Hle : m <= k. { exact nat_In_ordsucc_Le k Hko m Hmk. }
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

Theorem SNo_sub_add_R : forall a b, SNo a -> SNo b -> (a + b) + - b = a.
let a b. assume Ha Hb.
exact add_SNo_minus_R2 a b Ha Hb.
Qed.

Theorem SNo_add_cancel_R : forall a b c, SNo a -> SNo b -> SNo c -> a + c = b + c -> a = b.
let a b c. assume Ha Hb Hc Heq.
rewrite <- add_SNo_minus_R2 a c Ha Hc.
rewrite Heq.
exact add_SNo_minus_R2 b c Hb Hc.
Qed.

Theorem SNo_add_cancel_L : forall a b c, SNo a -> SNo b -> SNo c -> c + a = c + b -> a = b.
let a b c. assume Ha Hb Hc Heq.
apply SNo_add_cancel_R a b c Ha Hb Hc.
rewrite add_SNo_com a c Ha Hc.
rewrite add_SNo_com b c Hb Hc.
exact Heq.
Qed.

Theorem nat_sub_omega : forall m :e omega, forall n :e omega, m <= n -> n + - m :e omega.
let m. assume Hm.
apply nat_ind (fun k => forall n :e omega, k <= n -> n + - k :e omega).
- let n. assume Hn Hle.
  rewrite minus_SNo_0.
  rewrite add_SNo_0R n (omega_SNo n Hn).
  exact Hn.
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
    - assume H1 : p :e k.
      apply FalseE.
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

Theorem nat_In_sub_add : forall n :e omega, forall d :e omega, d <= n -> forall i :e n + - d, d + i :e n.
let n. assume Hn. let d. assume Hd Hle. let i. assume Hi.
claim Hsub : n + - d :e omega. { exact nat_sub_omega d Hd n Hn Hle. }
claim Hio : i :e omega. { exact nat_In_omega (n + - d) Hsub i Hi. }
claim Hilt : i < n + - d. { exact nat_In_SNoLt (n + - d) Hsub i Hi. }
apply nat_SNoLt_In n Hn (d + i) (nat_add_omega d Hd i Hio).
rewrite <- SNo_add_sub_L n d (omega_SNo n Hn) (omega_SNo d Hd).
exact add_SNo_Lt2 d i (n + - d) (omega_SNo d Hd) (omega_SNo i Hio) (omega_SNo (n + - d) Hsub) Hilt.
Qed.

Theorem nat_sub_Le : forall n :e omega, forall d :e omega, d <= n -> n + - d <= n.
let n. assume Hn. let d. assume Hd Hle.
claim Hsub : n + - d :e omega. { exact nat_sub_omega d Hd n Hn Hle. }
rewrite <- SNo_add_sub_L n d (omega_SNo n Hn) (omega_SNo d Hd) at 2.
rewrite <- add_SNo_0L (n + - d) (omega_SNo (n + - d) Hsub) at 1.
exact add_SNo_Le1 0 (n + - d) d SNo_0 (omega_SNo (n + - d) Hsub) (omega_SNo d Hd) (nat_0_Le d Hd).
Qed.

Theorem nat_least_witness : forall P:set -> prop, forall n :e omega,
  exists d :e ordsucc n, (forall j :e d, ~(P j)) /\ (d = n \/ P d).
let P. let n. assume Hn.
apply nat_ind (fun m => exists d :e ordsucc m, (forall j :e d, ~(P j)) /\ (d = m \/ P d)).
- prove exists d :e ordsucc 0, (forall j :e d, ~(P j)) /\ (d = 0 \/ P d).
  witness 0. apply andI.
  + exact ordsuccI2 0.
  + apply andI.
    * let j. assume Hj. apply FalseE. exact EmptyE j Hj.
    * apply orIL. reflexivity.
- let m. assume Hm IH.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  prove exists d :e ordsucc (ordsucc m), (forall j :e d, ~(P j)) /\ (d = ordsucc m \/ P d).
  apply IH. let d. assume Hd. apply Hd. assume Hdin Hspec. apply Hspec. assume Hall Hor.
  apply Hor.
  + assume Heq : d = m.
    apply xm (P m).
    * assume HPm : P m.
      witness m. apply andI.
      { exact ordsuccI1 (ordsucc m) m (ordsuccI2 m). }
      { apply andI.
        - rewrite <- Heq. exact Hall.
        - apply orIR. exact HPm. }
    * assume HnPm : ~(P m).
      witness (ordsucc m). apply andI.
      { exact ordsuccI2 (ordsucc m). }
      { apply andI.
        - let j. assume Hj.
          apply ordsuccE m j Hj.
          + assume Hjm : j :e m.
            claim Hjd : j :e d. { rewrite Heq. exact Hjm. }
            exact Hall j Hjd.
          + assume Hjeq : j = m. rewrite Hjeq. exact HnPm.
        - apply orIL. reflexivity. }
  + assume HPd : P d.
    witness d. apply andI.
    * exact ordsuccI1 (ordsucc m) d Hdin.
    * apply andI.
      { exact Hall. }
      { apply orIR. exact HPd. }
- exact omega_nat_p n Hn.
Qed.

Theorem nat_least_witness_unique : forall P:set -> prop, forall n :e omega,
  forall d1 :e ordsucc n, forall d2 :e ordsucc n,
  ((forall j :e d1, ~(P j)) /\ (d1 = n \/ P d1)) ->
  ((forall j :e d2, ~(P j)) /\ (d2 = n \/ P d2)) ->
  d1 = d2.
let P. let n. assume Hn. let d1. assume Hd1. let d2. assume Hd2.
assume Hs1 Hs2.
apply Hs1. assume Hall1 Hor1. apply Hs2. assume Hall2 Hor2.
claim Hd1o : d1 :e omega. { exact nat_In_omega (ordsucc n) (omega_ordsucc n Hn) d1 Hd1. }
claim Hd2o : d2 :e omega. { exact nat_In_omega (ordsucc n) (omega_ordsucc n Hn) d2 Hd2. }
apply ordinal_trichotomy_or_impred d1 d2 (nat_p_ordinal d1 (omega_nat_p d1 Hd1o)) (nat_p_ordinal d2 (omega_nat_p d2 Hd2o)).
- assume H12 : d1 :e d2.
  apply FalseE.
  apply Hor1.
  + assume Heq : d1 = n.
    claim Hn2 : n :e d2. { rewrite <- Heq. exact H12. }
    claim Hle2 : d2 <= n. { exact nat_In_ordsucc_Le n Hn d2 Hd2. }
    exact SNoLt_irref n (SNoLtLe_tra n d2 n (omega_SNo n Hn) (omega_SNo d2 Hd2o) (omega_SNo n Hn) (nat_In_SNoLt d2 Hd2o n Hn2) Hle2).
  + assume HP1 : P d1. exact Hall2 d1 H12 HP1.
- assume Heq : d1 = d2. exact Heq.
- assume H21 : d2 :e d1.
  apply FalseE.
  apply Hor2.
  + assume Heq : d2 = n.
    claim Hn1 : n :e d1. { rewrite <- Heq. exact H21. }
    claim Hle1 : d1 <= n. { exact nat_In_ordsucc_Le n Hn d1 Hd1. }
    exact SNoLt_irref n (SNoLtLe_tra n d1 n (omega_SNo n Hn) (omega_SNo d1 Hd1o) (omega_SNo n Hn) (nat_In_SNoLt d1 Hd1o n Hn1) Hle1).
  + assume HP2 : P d2. exact Hall1 d2 H21 HP2.
Qed.

(** ---- Part 2: Finite Message Sequences & Iter Roles ----------------------- *)

Definition RoleUser : set := 0.
Definition RoleSystem : set := 1.
Definition RoleAssistant : set := 2.
Definition RoleTool : set := 3.
Definition RoleRaw : set := 4.

Theorem RoleAssistant_neq_Tool : RoleAssistant <> RoleTool.
assume Heq : 2 = 3.
apply SNoLt_irref 2.
rewrite Heq at 2.
exact nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 2 In_2_3.
Qed.

Theorem RoleUser_neq_Tool : RoleUser <> RoleTool.
assume Heq : 0 = 3.
apply SNoLt_irref 0.
rewrite Heq at 2.
exact nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 0 In_0_3.
Qed.

Definition Msg : set -> set -> set := fun r c => setsum r c.
Definition msg_role : set -> set := fun m => proj0 m.
Definition msg_content : set -> set := fun m => proj1 m.

Theorem msg_role_pair : forall r c, msg_role (Msg r c) = r.
let r c. exact proj0_pair_eq r c.
Qed.

Theorem msg_content_pair : forall r c, msg_content (Msg r c) = c.
let r c. exact proj1_pair_eq r c.
Qed.

Definition Seq : set -> (set -> set) -> set := fun n f => setsum n (fun i :e n => f i).
Definition seq_len : set -> set := fun s => proj0 s.
Definition seq_at : set -> set -> set := fun s i => ap (proj1 s) i.
Definition ValidSeq : set -> prop := fun s => seq_len s :e omega.

Theorem seq_len_mk : forall n, forall f:set -> set, seq_len (Seq n f) = n.
let n f. exact proj0_pair_eq n (fun i :e n => f i).
Qed.

Theorem seq_at_mk : forall n, forall f:set -> set, forall i :e n, seq_at (Seq n f) i = f i.
let n f. let i. assume Hi.
prove ap (proj1 (setsum n (fun j :e n => f j))) i = f i.
rewrite proj1_pair_eq n (fun j :e n => f j).
exact beta n f i Hi.
Qed.

Theorem ValidSeq_mk : forall n :e omega, forall f:set -> set, ValidSeq (Seq n f).
let n. assume Hn. let f.
prove seq_len (Seq n f) :e omega.
rewrite seq_len_mk n f. exact Hn.
Qed.

Definition seq_take : set -> set -> set :=
  fun k s => Seq k (fun i => seq_at s i).

Definition seq_drop : set -> set -> set :=
  fun d s => Seq (seq_len s + - d) (fun i => seq_at s (d + i)).

(** Cleanup rule from iter.metta:67-79, parameterized by pure truncation/stripping *)
Variable trunc_tool : set -> set.
Variable strip_reasoning : set -> set.

Definition clean_msg : set -> set :=
  fun m =>
    if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
    else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
    else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
    else m.

Theorem clean_msg_preserves_role : forall m, msg_role (clean_msg m) = msg_role m.
let m.
apply xm (msg_role m = RoleTool).
- assume H : msg_role m = RoleTool.
  prove msg_role (if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
                  else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
                  else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
                  else m) = msg_role m.
  rewrite If_i_1 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
          (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
           else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) H.
  rewrite msg_role_pair RoleTool (trunc_tool (msg_content m)).
  symmetry. exact H.
- assume Hnt : msg_role m <> RoleTool.
  prove msg_role (if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
                  else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
                  else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
                  else m) = msg_role m.
  rewrite If_i_0 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
          (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
           else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hnt.
  apply xm (msg_role m = RoleAssistant).
  + assume Ha : msg_role m = RoleAssistant.
    rewrite If_i_1 (msg_role m = RoleAssistant) (Msg RoleAssistant (strip_reasoning (msg_content m)))
            (if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Ha.
    rewrite msg_role_pair RoleAssistant (strip_reasoning (msg_content m)).
    symmetry. exact Ha.
  + assume Hna : msg_role m <> RoleAssistant.
    rewrite If_i_0 (msg_role m = RoleAssistant) (Msg RoleAssistant (strip_reasoning (msg_content m)))
            (if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hna.
    apply xm (msg_role m = RoleRaw).
    * assume Hr : msg_role m = RoleRaw.
      rewrite If_i_1 (msg_role m = RoleRaw) (Msg RoleRaw (strip_reasoning (msg_content m))) m Hr.
      rewrite msg_role_pair RoleRaw (strip_reasoning (msg_content m)).
      symmetry. exact Hr.
    * assume Hnr : msg_role m <> RoleRaw.
      rewrite If_i_0 (msg_role m = RoleRaw) (Msg RoleRaw (strip_reasoning (msg_content m))) m Hnr.
      reflexivity.
Qed.

Definition cleanup_old_messages : set -> set -> set :=
  fun preserve s =>
    Seq (seq_len s) (fun i => if i + preserve < seq_len s then clean_msg (seq_at s i) else seq_at s i).

(** ToolPaired invariant: every Tool message has a positive index i = k + 1
    and its immediate predecessor at k is either Assistant or Tool.
    By induction this guarantees no leading Tool and every Tool belongs to a
    contiguous Assistant-then-Tool block with no intervening User/System/Raw. *)
Definition ToolPaired : set -> prop :=
  fun s =>
    forall i :e seq_len s, msg_role (seq_at s i) = RoleTool ->
      0 < i /\ (exists k :e omega, i = k + 1 /\
        (msg_role (seq_at s k) = RoleAssistant \/ msg_role (seq_at s k) = RoleTool)).

Definition NoLeadingTool : set -> prop :=
  fun s => seq_len s = 0 \/ msg_role (seq_at s 0) <> RoleTool.

Theorem ToolPaired_implies_NoLeadingTool : forall s, ValidSeq s -> ToolPaired s -> NoLeadingTool s.
let s. assume Hs Htp.
apply xm (seq_len s = 0).
- assume H0 : seq_len s = 0. exact orIL (seq_len s = 0) (msg_role (seq_at s 0) <> RoleTool) H0.
- assume Hne : seq_len s <> 0.
  prove seq_len s = 0 \/ msg_role (seq_at s 0) <> RoleTool.
  apply orIR.
  assume Htool : msg_role (seq_at s 0) = RoleTool.
  claim Hpos : 0 < seq_len s.
  { apply nat_SNoLe_cases 0 nat_0_omega (seq_len s) Hs (nat_0_Le (seq_len s) Hs).
    - assume H0in : 0 :e seq_len s. exact nat_In_SNoLt (seq_len s) Hs 0 H0in.
    - assume H0eq : 0 = seq_len s. apply FalseE. apply Hne. symmetry. exact H0eq. }
  claim H0in : 0 :e seq_len s. { exact nat_SNoLt_In (seq_len s) Hs 0 nat_0_omega Hpos. }
  claim H0lt0 : 0 < 0. { exact andEL (0 < 0) (exists k :e omega, 0 = k + 1 /\ (msg_role (seq_at s k) = RoleAssistant \/ msg_role (seq_at s k) = RoleTool)) (Htp 0 H0in Htool). }
  exact SNoLt_irref 0 H0lt0.
Qed.

(** ---- Theorem Group 1: cleanup_old_messages Guarantees -------------------- *)

Theorem cleanup_preserves_len : forall P s, seq_len (cleanup_old_messages P s) = seq_len s.
let P s. exact seq_len_mk (seq_len s) (fun i => if i + P < seq_len s then clean_msg (seq_at s i) else seq_at s i).
Qed.

Theorem cleanup_preserves_recent : forall P :e omega, forall s, ValidSeq s ->
  forall i :e seq_len s, seq_len s <= i + P ->
  seq_at (cleanup_old_messages P s) i = seq_at s i.
let P. assume HP. let s. assume Hs. let i. assume Hi Hge.
claim Hio : i :e omega. { exact nat_In_omega (seq_len s) Hs i Hi. }
claim Hnlt : ~(i + P < seq_len s).
{ assume Hlt : i + P < seq_len s.
  exact SNoLt_irref (seq_len s)
        (SNoLeLt_tra (seq_len s) (i + P) (seq_len s) (omega_SNo (seq_len s) Hs)
          (omega_SNo (i + P) (nat_add_omega i Hio P HP)) (omega_SNo (seq_len s) Hs) Hge Hlt). }
prove seq_at (Seq (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j)) i = seq_at s i.
rewrite seq_at_mk (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j) i Hi.
exact If_i_0 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hnlt.
Qed.

Theorem cleanup_preserves_roles : forall P s, forall i :e seq_len s,
  msg_role (seq_at (cleanup_old_messages P s) i) = msg_role (seq_at s i).
let P s. let i. assume Hi.
prove msg_role (seq_at (Seq (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j)) i) = msg_role (seq_at s i).
rewrite seq_at_mk (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j) i Hi.
apply xm (i + P < seq_len s).
- assume Hlt : i + P < seq_len s.
  rewrite If_i_1 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hlt.
  exact clean_msg_preserves_role (seq_at s i).
- assume Hnlt : ~(i + P < seq_len s).
  rewrite If_i_0 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hnlt.
  reflexivity.
Qed.

Theorem cleanup_preserves_ToolPaired : forall P s, ValidSeq s -> ToolPaired s -> ToolPaired (cleanup_old_messages P s).
let P s. assume Hs Htp.
let i. assume Hi Htool.
claim Hi' : i :e seq_len s. { rewrite <- cleanup_preserves_len P s. exact Hi. }
claim Htool' : msg_role (seq_at s i) = RoleTool.
{ rewrite <- cleanup_preserves_roles P s i Hi'. exact Htool. }
apply Htp i Hi' Htool'. assume Hpos Hex.
apply andI.
- exact Hpos.
- apply Hex. let k. assume Hk. apply Hk. assume Hko Hk2. apply Hk2. assume Hik Hor.
  claim Hkin : k :e seq_len s.
  { apply nat_SNoLt_In (seq_len s) Hs k Hko.
    apply SNoLt_tra k i (seq_len s) (omega_SNo k Hko) (omega_SNo i (nat_In_omega (seq_len s) Hs i Hi')) (omega_SNo (seq_len s) Hs).
    - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
      exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
    - exact nat_In_SNoLt (seq_len s) Hs i Hi'. }
  witness k. apply andI.
  + exact Hko.
  + apply andI.
    * exact Hik.
    * rewrite cleanup_preserves_roles P s k Hkin. exact Hor.
Qed.

(** ---- Theorem Group 2: drop_leading_tool_messages & ToolPaired Recovery --- *)

Definition lead_tool_cut : set -> set :=
  fun s => Eps_i (fun d => d :e ordsucc (seq_len s) /\
    (forall j :e d, msg_role (seq_at s j) = RoleTool) /\
    (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool)).

Theorem lead_tool_cut_spec : forall s, ValidSeq s ->
  lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
let s. assume Hs.
claim Hex : exists d, d :e ordsucc (seq_len s) /\
  (forall j :e d, msg_role (seq_at s j) = RoleTool) /\
  (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool).
{ apply nat_least_witness (fun j => msg_role (seq_at s j) <> RoleTool) (seq_len s) Hs.
  let d. assume Hd. apply Hd. assume Hdin Hrest. apply Hrest. assume Hall Hor.
  witness d. apply andI.
  - apply andI.
    + exact Hdin.
    + let j. assume Hj.
      apply xm (msg_role (seq_at s j) = RoleTool).
      * assume H : msg_role (seq_at s j) = RoleTool. exact H.
      * assume Hne : msg_role (seq_at s j) <> RoleTool. apply FalseE. exact Hall j Hj Hne.
  - exact Hor. }
exact Eps_i_ex (fun d => d :e ordsucc (seq_len s) /\
  (forall j :e d, msg_role (seq_at s j) = RoleTool) /\
  (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool)) Hex.
Qed.

Theorem lead_tool_cut_eq : forall s, ValidSeq s -> forall d :e ordsucc (seq_len s),
  (forall j :e d, msg_role (seq_at s j) = RoleTool) ->
  (d = seq_len s \/ msg_role (seq_at s d) <> RoleTool) ->
  lead_tool_cut s = d.
let s. assume Hs. let d. assume Hdin Hall Hor.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 Hcor. apply Hc12. assume Hcin Hcall.
apply nat_least_witness_unique (fun j => msg_role (seq_at s j) <> RoleTool) (seq_len s) Hs (lead_tool_cut s) Hcin d Hdin.
- apply andI.
  + let j. assume Hj Hne. exact Hne (Hcall j Hj).
  + exact Hcor.
- apply andI.
  + let j. assume Hj Hne. exact Hne (Hall j Hj).
  + exact Hor.
Qed.

Definition drop_leading_tools : set -> set :=
  fun s => seq_drop (lead_tool_cut s) s.

Theorem drop_leading_tools_valid : forall s, ValidSeq s -> ValidSeq (drop_leading_tools s).
let s. assume Hs.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
exact ValidSeq_mk (seq_len s + - lead_tool_cut s) (nat_sub_omega (lead_tool_cut s) Hco (seq_len s) Hs Hcle)
      (fun i => seq_at s (lead_tool_cut s + i)).
Qed.

Theorem drop_leading_tools_len_le : forall s, ValidSeq s -> seq_len (drop_leading_tools s) <= seq_len s.
let s. assume Hs.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
prove seq_len (Seq (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i))) <= seq_len s.
rewrite seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)).
exact nat_sub_Le (seq_len s) Hs (lead_tool_cut s) Hco Hcle.
Qed.

Theorem drop_leading_tools_NoLeadingTool : forall s, ValidSeq s -> NoLeadingTool (drop_leading_tools s).
let s. assume Hs.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 Hcor. apply Hc12. assume Hcin Hcall.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
claim Hlen : seq_len (drop_leading_tools s) = seq_len s + - lead_tool_cut s.
{ exact seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)). }
apply Hcor.
- assume Heq : lead_tool_cut s = seq_len s.
  prove seq_len (drop_leading_tools s) = 0 \/ msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool.
  apply orIL.
  rewrite Hlen. rewrite Heq.
  exact add_SNo_minus_SNo_rinv (seq_len s) (omega_SNo (seq_len s) Hs).
- assume Hne : msg_role (seq_at s (lead_tool_cut s)) <> RoleTool.
  apply xm (seq_len (drop_leading_tools s) = 0).
  + assume H0 : seq_len (drop_leading_tools s) = 0.
    exact orIL (seq_len (drop_leading_tools s) = 0) (msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool) H0.
  + assume Hne0 : seq_len (drop_leading_tools s) <> 0.
    prove seq_len (drop_leading_tools s) = 0 \/ msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool.
    apply orIR.
    claim Hsub : seq_len s + - lead_tool_cut s :e omega. { exact nat_sub_omega (lead_tool_cut s) Hco (seq_len s) Hs Hcle. }
    claim H0in : 0 :e seq_len s + - lead_tool_cut s.
    { apply nat_SNoLe_cases 0 nat_0_omega (seq_len s + - lead_tool_cut s) Hsub (nat_0_Le (seq_len s + - lead_tool_cut s) Hsub).
      - assume H : 0 :e seq_len s + - lead_tool_cut s. exact H.
      - assume H0 : 0 = seq_len s + - lead_tool_cut s.
        apply FalseE. apply Hne0. rewrite Hlen. symmetry. exact H0. }
    prove msg_role (seq_at (Seq (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i))) 0) <> RoleTool.
    rewrite seq_at_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)) 0 H0in.
    rewrite add_SNo_0R (lead_tool_cut s) (omega_SNo (lead_tool_cut s) Hco).
    exact Hne.
Qed.

Theorem drop_leading_tools_idempotent : forall s, ValidSeq s ->
  drop_leading_tools (drop_leading_tools s) = drop_leading_tools s.
let s. assume Hs.
claim Ht : ValidSeq (drop_leading_tools s). { exact drop_leading_tools_valid s Hs. }
claim Hnlt : NoLeadingTool (drop_leading_tools s). { exact drop_leading_tools_NoLeadingTool s Hs. }
claim Hcut0 : lead_tool_cut (drop_leading_tools s) = 0.
{ apply lead_tool_cut_eq (drop_leading_tools s) Ht 0 (nat_Le_In_ordsucc 0 nat_0_omega (seq_len (drop_leading_tools s)) Ht (nat_0_Le (seq_len (drop_leading_tools s)) Ht)).
  - let j. assume Hj. apply FalseE. exact EmptyE j Hj.
  - apply Hnlt.
    + assume H0 : seq_len (drop_leading_tools s) = 0. apply orIL. symmetry. exact H0.
    + assume Hne : msg_role (seq_at (drop_leading_tools s) 0) <> RoleTool. apply orIR. exact Hne. }
claim Hlen : seq_len (drop_leading_tools s) + - 0 = seq_len (drop_leading_tools s).
{ rewrite minus_SNo_0. exact add_SNo_0R (seq_len (drop_leading_tools s)) (omega_SNo (seq_len (drop_leading_tools s)) Ht). }
prove setsum (seq_len (drop_leading_tools s) + - lead_tool_cut (drop_leading_tools s))
             (fun i :e seq_len (drop_leading_tools s) + - lead_tool_cut (drop_leading_tools s) =>
               seq_at (drop_leading_tools s) (lead_tool_cut (drop_leading_tools s) + i))
    = drop_leading_tools s.
rewrite Hcut0. rewrite Hlen.
claim Hspec : lead_tool_cut s :e ordsucc (seq_len s) /\
  (forall j :e lead_tool_cut s, msg_role (seq_at s j) = RoleTool) /\
  (lead_tool_cut s = seq_len s \/ msg_role (seq_at s (lead_tool_cut s)) <> RoleTool).
{ exact lead_tool_cut_spec s Hs. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut s :e omega. { exact nat_In_omega (ordsucc (seq_len s)) (omega_ordsucc (seq_len s) Hs) (lead_tool_cut s) Hcin. }
claim Hcle : lead_tool_cut s <= seq_len s. { exact nat_In_ordsucc_Le (seq_len s) Hs (lead_tool_cut s) Hcin. }
claim Hn' : seq_len (drop_leading_tools s) = seq_len s + - lead_tool_cut s.
{ exact seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)). }
claim Hlam : (fun i :e seq_len (drop_leading_tools s) => seq_at (drop_leading_tools s) (0 + i))
           = (fun i :e seq_len s + - lead_tool_cut s => seq_at s (lead_tool_cut s + i)).
{ rewrite Hn'.
  apply lam_ext (seq_len s + - lead_tool_cut s).
  let i. assume Hi.
  claim Hio : i :e omega. { exact nat_In_omega (seq_len s + - lead_tool_cut s) (nat_sub_omega (lead_tool_cut s) Hco (seq_len s) Hs Hcle) i Hi. }
  prove seq_at (drop_leading_tools s) (0 + i) = seq_at s (lead_tool_cut s + i).
  rewrite add_SNo_0L i (omega_SNo i Hio).
  exact seq_at_mk (seq_len s + - lead_tool_cut s) (fun j => seq_at s (lead_tool_cut s + j)) i Hi. }
rewrite Hlam. rewrite Hn'. reflexivity.
Qed.

(** Checkpoint prefix take preserves ToolPaired *)
Theorem seq_take_preserves_ToolPaired : forall s, ValidSeq s -> forall k :e omega, k <= seq_len s ->
  ToolPaired s -> ToolPaired (seq_take k s).
let s. assume Hs. let k. assume Hk Hkle Htp.
let i. assume Hi Htool.
claim Hik : i :e k. { rewrite <- seq_len_mk k (fun j => seq_at s j). exact Hi. }
claim Hio : i :e omega. { exact nat_In_omega k Hk i Hik. }
claim Hin : i :e seq_len s.
{ exact nat_SNoLt_In (seq_len s) Hs i Hio (SNoLtLe_tra i k (seq_len s) (omega_SNo i Hio) (omega_SNo k Hk) (omega_SNo (seq_len s) Hs) (nat_In_SNoLt k Hk i Hik) Hkle). }
claim Htool' : msg_role (seq_at s i) = RoleTool.
{ rewrite <- seq_at_mk k (fun j => seq_at s j) i Hik. exact Htool. }
apply Htp i Hin Htool'. assume Hpos Hex.
apply andI.
- exact Hpos.
- apply Hex. let p. assume Hp. apply Hp. assume Hpo Hp2. apply Hp2. assume Hip Hor.
  claim Hpk : p :e k.
  { apply nat_SNoLt_In k Hk p Hpo.
    apply SNoLt_tra p i k (omega_SNo p Hpo) (omega_SNo i Hio) (omega_SNo k Hk).
    - rewrite Hip. rewrite <- add_SNo_0R p (omega_SNo p Hpo) at 1.
      exact add_SNo_Lt2 p 0 1 (omega_SNo p Hpo) SNo_0 SNo_1 SNoLt_0_1.
    - exact nat_In_SNoLt k Hk i Hik. }
  witness p. apply andI.
  + exact Hpo.
  + apply andI.
    * exact Hip.
    * claim Hatp : seq_at (seq_take k s) p = seq_at s p. { exact seq_at_mk k (fun j => seq_at s j) p Hpk. }
      rewrite Hatp. exact Hor.
Qed.

(** MAIN THEOREM: Arbitrary prefix drop followed by drop_leading_tools ALWAYS restores ToolPaired! *)
Theorem drop_then_strip_preserves_ToolPaired : forall s, ValidSeq s -> forall d :e omega, d <= seq_len s ->
  ToolPaired s -> ToolPaired (drop_leading_tools (seq_drop d s)).
let s. assume Hs. let d. assume Hd Hdle Htp.
claim Hsub_o : seq_len s + - d :e omega. { exact nat_sub_omega d Hd (seq_len s) Hs Hdle. }
claim Hds : ValidSeq (seq_drop d s). { exact ValidSeq_mk (seq_len s + - d) Hsub_o (fun i => seq_at s (d + i)). }
claim Hnlt : NoLeadingTool (drop_leading_tools (seq_drop d s)). { exact drop_leading_tools_NoLeadingTool (seq_drop d s) Hds. }
claim Hspec : lead_tool_cut (seq_drop d s) :e ordsucc (seq_len (seq_drop d s)) /\
  (forall j :e lead_tool_cut (seq_drop d s), msg_role (seq_at (seq_drop d s) j) = RoleTool) /\
  (lead_tool_cut (seq_drop d s) = seq_len (seq_drop d s) \/ msg_role (seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s))) <> RoleTool).
{ exact lead_tool_cut_spec (seq_drop d s) Hds. }
apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
claim Hco : lead_tool_cut (seq_drop d s) :e omega.
{ exact nat_In_omega (ordsucc (seq_len (seq_drop d s))) (omega_ordsucc (seq_len (seq_drop d s)) Hds) (lead_tool_cut (seq_drop d s)) Hcin. }
claim Hcle : lead_tool_cut (seq_drop d s) <= seq_len (seq_drop d s).
{ exact nat_In_ordsucc_Le (seq_len (seq_drop d s)) Hds (lead_tool_cut (seq_drop d s)) Hcin. }
claim Hds_len : seq_len (seq_drop d s) = seq_len s + - d. { exact seq_len_mk (seq_len s + - d) (fun i => seq_at s (d + i)). }
claim Hfin_v : ValidSeq (drop_leading_tools (seq_drop d s)). { exact drop_leading_tools_valid (seq_drop d s) Hds. }
claim Hfin_len : seq_len (drop_leading_tools (seq_drop d s)) = seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s).
{ exact seq_len_mk (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun i => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + i)). }
let i. assume Hi Htool.
claim Hio : i :e omega. { exact nat_In_omega (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v i Hi. }
claim Hipos : 0 < i.
{ apply nat_SNoLe_cases 0 nat_0_omega i Hio (nat_0_Le i Hio).
  - assume H0i : 0 :e i. exact nat_In_SNoLt i Hio 0 H0i.
  - assume H0eq : 0 = i.
    apply FalseE.
    apply Hnlt.
    + assume Hlen0 : seq_len (drop_leading_tools (seq_drop d s)) = 0.
      claim Hie : i :e 0. { rewrite <- Hlen0. exact Hi. }
      exact EmptyE i Hie.
    + assume Hne0 : msg_role (seq_at (drop_leading_tools (seq_drop d s)) 0) <> RoleTool.
      apply Hne0. rewrite H0eq. exact Htool. }
apply nat_pos_pred i Hio Hipos. let k. assume Hk. apply Hk. assume Hko Hik.
claim Hki_in : k :e seq_len (drop_leading_tools (seq_drop d s)).
{ apply nat_SNoLt_In (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v k Hko.
  apply SNoLt_tra k i (seq_len (drop_leading_tools (seq_drop d s))) (omega_SNo k Hko) (omega_SNo i Hio) (omega_SNo (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v).
  - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
    exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
  - exact nat_In_SNoLt (seq_len (drop_leading_tools (seq_drop d s))) Hfin_v i Hi. }
claim Hi_sub : i :e seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s).
{ rewrite <- Hfin_len. exact Hi. }
claim Hk_sub : k :e seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s).
{ rewrite <- Hfin_len. exact Hki_in. }
claim Hci_in : lead_tool_cut (seq_drop d s) + i :e seq_len (seq_drop d s).
{ exact nat_In_sub_add (seq_len (seq_drop d s)) Hds (lead_tool_cut (seq_drop d s)) Hco Hcle i Hi_sub. }
claim Hck_in : lead_tool_cut (seq_drop d s) + k :e seq_len (seq_drop d s).
{ exact nat_In_sub_add (seq_len (seq_drop d s)) Hds (lead_tool_cut (seq_drop d s)) Hco Hcle k Hk_sub. }
claim Hci_sub : lead_tool_cut (seq_drop d s) + i :e seq_len s + - d. { rewrite <- Hds_len. exact Hci_in. }
claim Hck_sub : lead_tool_cut (seq_drop d s) + k :e seq_len s + - d. { rewrite <- Hds_len. exact Hck_in. }
claim Hdci_in : d + (lead_tool_cut (seq_drop d s) + i) :e seq_len s.
{ exact nat_In_sub_add (seq_len s) Hs d Hd Hdle (lead_tool_cut (seq_drop d s) + i) Hci_sub. }
claim Hat_i : seq_at (drop_leading_tools (seq_drop d s)) i = seq_at s (d + (lead_tool_cut (seq_drop d s) + i)).
{ prove seq_at (Seq (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j))) i
      = seq_at s (d + (lead_tool_cut (seq_drop d s) + i)).
  rewrite seq_at_mk (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j)) i Hi_sub.
  exact seq_at_mk (seq_len s + - d) (fun j => seq_at s (d + j)) (lead_tool_cut (seq_drop d s) + i) Hci_sub. }
claim Hat_k : seq_at (drop_leading_tools (seq_drop d s)) k = seq_at s (d + (lead_tool_cut (seq_drop d s) + k)).
{ prove seq_at (Seq (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j))) k
      = seq_at s (d + (lead_tool_cut (seq_drop d s) + k)).
  rewrite seq_at_mk (seq_len (seq_drop d s) + - lead_tool_cut (seq_drop d s)) (fun j => seq_at (seq_drop d s) (lead_tool_cut (seq_drop d s) + j)) k Hk_sub.
  exact seq_at_mk (seq_len s + - d) (fun j => seq_at s (d + j)) (lead_tool_cut (seq_drop d s) + k) Hck_sub. }
claim Htool_s : msg_role (seq_at s (d + (lead_tool_cut (seq_drop d s) + i))) = RoleTool.
{ rewrite <- Hat_i. exact Htool. }
apply Htp (d + (lead_tool_cut (seq_drop d s) + i)) Hdci_in Htool_s. assume Hpos_s Hex_s.
apply Hex_s. let p. assume Hp. apply Hp. assume Hpo Hp2. apply Hp2. assume Heqp Hor_s.
claim Hidx_eq : d + (lead_tool_cut (seq_drop d s) + i) = (d + (lead_tool_cut (seq_drop d s) + k)) + 1.
{ rewrite Hik.
  rewrite add_SNo_assoc (lead_tool_cut (seq_drop d s)) k 1 (omega_SNo (lead_tool_cut (seq_drop d s)) Hco) (omega_SNo k Hko) SNo_1.
  exact add_SNo_assoc d (lead_tool_cut (seq_drop d s) + k) 1 (omega_SNo d Hd) (omega_SNo (lead_tool_cut (seq_drop d s) + k) (nat_add_omega (lead_tool_cut (seq_drop d s)) Hco k Hko)) SNo_1. }
claim Hpeq : p = d + (lead_tool_cut (seq_drop d s) + k).
{ apply SNo_add_cancel_R p (d + (lead_tool_cut (seq_drop d s) + k)) 1
        (omega_SNo p Hpo) (omega_SNo (d + (lead_tool_cut (seq_drop d s) + k)) (nat_add_omega d Hd (lead_tool_cut (seq_drop d s) + k) (nat_add_omega (lead_tool_cut (seq_drop d s)) Hco k Hko))) SNo_1.
  rewrite <- Heqp. exact Hidx_eq. }
apply andI.
- exact Hipos.
- witness k. apply andI.
  + exact Hko.
  + apply andI.
    * exact Hik.
    * rewrite Hat_k. rewrite <- Hpeq. exact Hor_s.
Qed.

(** ---- Theorem Group 3: Iter Windowing Bound (MAX=100, RETAIN=80) ---------- *)

Definition window_trim : set -> set -> set -> set :=
  fun M R s => if M <= seq_len s then seq_drop (seq_len s + - R) s else s.

Definition hygiene_step : set -> set -> set -> set :=
  fun M R s => drop_leading_tools (window_trim M R s).

Theorem hygiene_step_bounded_and_paired : forall M :e omega, forall R :e omega, R < M ->
  forall s, ValidSeq s -> ToolPaired s ->
  ValidSeq (hygiene_step M R s) /\ seq_len (hygiene_step M R s) < M /\ ToolPaired (hygiene_step M R s).
let M. assume HM. let R. assume HR HRM. let s. assume Hs Htp.
apply xm (M <= seq_len s).
- assume Hge : M <= seq_len s.
  claim Htrim : window_trim M R s = seq_drop (seq_len s + - R) s.
  { exact If_i_1 (M <= seq_len s) (seq_drop (seq_len s + - R) s) s Hge. }
  claim HRle : R <= seq_len s.
  { exact SNoLtLe R (seq_len s) (SNoLtLe_tra R M (seq_len s) (omega_SNo R HR) (omega_SNo M HM) (omega_SNo (seq_len s) Hs) HRM Hge). }
  claim Hd_o : seq_len s + - R :e omega. { exact nat_sub_omega R HR (seq_len s) Hs HRle. }
  claim Hd_le : seq_len s + - R <= seq_len s. { exact nat_sub_Le (seq_len s) Hs R HR HRle. }
  claim Hw_len : seq_len (seq_drop (seq_len s + - R) s) = R.
  { prove seq_len (Seq (seq_len s + - (seq_len s + - R)) (fun i => seq_at s ((seq_len s + - R) + i))) = R.
    rewrite seq_len_mk (seq_len s + - (seq_len s + - R)) (fun i => seq_at s ((seq_len s + - R) + i)).
    rewrite minus_add_SNo_distr (seq_len s) (- R) (omega_SNo (seq_len s) Hs) (SNo_minus_SNo R (omega_SNo R HR)).
    rewrite minus_SNo_invol R (omega_SNo R HR).
    exact add_SNo_minus_L2' (seq_len s) R (omega_SNo (seq_len s) Hs) (omega_SNo R HR). }
  claim Hw_v : ValidSeq (seq_drop (seq_len s + - R) s).
  { prove seq_len (seq_drop (seq_len s + - R) s) :e omega. rewrite Hw_len. exact HR. }
  prove ValidSeq (drop_leading_tools (window_trim M R s)) /\
        seq_len (drop_leading_tools (window_trim M R s)) < M /\
        ToolPaired (drop_leading_tools (window_trim M R s)).
  rewrite Htrim.
  apply and3I.
  + exact drop_leading_tools_valid (seq_drop (seq_len s + - R) s) Hw_v.
  + apply SNoLeLt_tra (seq_len (drop_leading_tools (seq_drop (seq_len s + - R) s))) R M
          (omega_SNo (seq_len (drop_leading_tools (seq_drop (seq_len s + - R) s))) (drop_leading_tools_valid (seq_drop (seq_len s + - R) s) Hw_v))
          (omega_SNo R HR) (omega_SNo M HM).
    * rewrite <- Hw_len at 2. exact drop_leading_tools_len_le (seq_drop (seq_len s + - R) s) Hw_v.
    * exact HRM.
  + exact drop_then_strip_preserves_ToolPaired s Hs (seq_len s + - R) Hd_o Hd_le Htp.
- assume Hnge : ~(M <= seq_len s).
  claim HltM : seq_len s < M.
  { apply ordinal_trichotomy_or_impred (seq_len s) M (nat_p_ordinal (seq_len s) (omega_nat_p (seq_len s) Hs)) (nat_p_ordinal M (omega_nat_p M HM)).
    - assume H : seq_len s :e M. exact nat_In_SNoLt M HM (seq_len s) H.
    - assume H : seq_len s = M. apply FalseE. apply Hnge. rewrite H. exact SNoLe_ref M.
    - assume H : M :e seq_len s. apply FalseE. apply Hnge. exact SNoLtLe M (seq_len s) (nat_In_SNoLt (seq_len s) Hs M H). }
  claim Htrim : window_trim M R s = s.
  { exact If_i_0 (M <= seq_len s) (seq_drop (seq_len s + - R) s) s Hnge. }
  prove ValidSeq (drop_leading_tools (window_trim M R s)) /\
        seq_len (drop_leading_tools (window_trim M R s)) < M /\
        ToolPaired (drop_leading_tools (window_trim M R s)).
  rewrite Htrim.
  claim Hcut0 : lead_tool_cut s = 0.
  { apply lead_tool_cut_eq s Hs 0 (nat_Le_In_ordsucc 0 nat_0_omega (seq_len s) Hs (nat_0_Le (seq_len s) Hs)).
    - let j. assume Hj. apply FalseE. exact EmptyE j Hj.
    - apply ToolPaired_implies_NoLeadingTool s Hs Htp.
      + assume H0 : seq_len s = 0. apply orIL. symmetry. exact H0.
      + assume Hne : msg_role (seq_at s 0) <> RoleTool. apply orIR. exact Hne. }
  claim Hlen_eq : seq_len (drop_leading_tools s) = seq_len s.
  { prove seq_len (Seq (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i))) = seq_len s.
    rewrite seq_len_mk (seq_len s + - lead_tool_cut s) (fun i => seq_at s (lead_tool_cut s + i)).
    rewrite Hcut0. rewrite minus_SNo_0. exact add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hs). }
  apply and3I.
  + exact drop_leading_tools_valid s Hs.
  + rewrite Hlen_eq. exact HltM.
  + let i. assume Hi Htool.
    claim Hi' : i :e seq_len s. { rewrite <- Hlen_eq. exact Hi. }
    claim Hat : forall j :e seq_len s, seq_at (drop_leading_tools s) j = seq_at s j.
    { let j. assume Hj.
      claim Hjo : j :e omega. { exact nat_In_omega (seq_len s) Hs j Hj. }
      claim Hj' : j :e seq_len s + - lead_tool_cut s.
      { rewrite Hcut0. rewrite minus_SNo_0. rewrite add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hs). exact Hj. }
      prove seq_at (Seq (seq_len s + - lead_tool_cut s) (fun u => seq_at s (lead_tool_cut s + u))) j = seq_at s j.
      rewrite seq_at_mk (seq_len s + - lead_tool_cut s) (fun u => seq_at s (lead_tool_cut s + u)) j Hj'.
      rewrite Hcut0. rewrite add_SNo_0L j (omega_SNo j Hjo). reflexivity. }
    claim Htool' : msg_role (seq_at s i) = RoleTool. { rewrite <- Hat i Hi'. exact Htool. }
    apply Htp i Hi' Htool'. assume Hpos Hex.
    apply andI.
    * exact Hpos.
    * apply Hex. let k. assume Hk. apply Hk. assume Hko Hk2. apply Hk2. assume Hik Hor.
      claim Hkin : k :e seq_len s.
      { apply nat_SNoLt_In (seq_len s) Hs k Hko.
        apply SNoLt_tra k i (seq_len s) (omega_SNo k Hko) (omega_SNo i (nat_In_omega (seq_len s) Hs i Hi')) (omega_SNo (seq_len s) Hs).
        - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
          exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
        - exact nat_In_SNoLt (seq_len s) Hs i Hi'. }
      witness k. apply andI.
      { exact Hko. }
      { apply andI.
        - exact Hik.
        - rewrite Hat k Hkin. exact Hor. }
Qed.

(** ---- Theorem Group 4: Constructive Bucket-Skip Witness (iter.metta:114-121) *)

Definition MAX_EXP : set := 5 * (10 + 10).
Definition RETAIN_EXP : set := 4 * (10 + 10).
Definition INTERVAL_EXP : set := 10 + 10.

Theorem n20_omega : INTERVAL_EXP :e omega.
exact nat_add_omega 10 (nat_p_omega 10 nat_10) 10 (nat_p_omega 10 nat_10).
Qed.

Theorem n80_omega : RETAIN_EXP :e omega.
exact nat_mul_omega 4 (nat_p_omega 4 nat_4) INTERVAL_EXP n20_omega.
Qed.

Theorem n100_omega : MAX_EXP :e omega.
exact nat_mul_omega 5 (nat_p_omega 5 nat_5) INTERVAL_EXP n20_omega.
Qed.

Theorem n100_eq_80_plus_20 : MAX_EXP = RETAIN_EXP + INTERVAL_EXP.
prove 5 * INTERVAL_EXP = 4 * INTERVAL_EXP + INTERVAL_EXP.
rewrite <- mul_nat_mul_SNo 5 (nat_p_omega 5 nat_5) INTERVAL_EXP n20_omega.
prove mul_nat (ordsucc 4) INTERVAL_EXP = 4 * INTERVAL_EXP + INTERVAL_EXP.
rewrite mul_nat_SL 4 nat_4 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega).
rewrite add_nat_add_SNo (mul_nat 4 INTERVAL_EXP) (nat_p_omega (mul_nat 4 INTERVAL_EXP) (mul_nat_p 4 nat_4 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega))) INTERVAL_EXP n20_omega.
rewrite mul_nat_mul_SNo 4 (nat_p_omega 4 nat_4) INTERVAL_EXP n20_omega.
reflexivity.
Qed.

Theorem n20_pos : 0 < INTERVAL_EXP.
claim H10o : 10 :e omega. { exact nat_p_omega 10 nat_10. }
claim H10p : 0 < 10.
{ exact nat_In_SNoLt 10 H10o 0 (nat_0_in_ordsucc 9 nat_9). }
prove 0 < 10 + 10.
apply SNoLt_tra 0 10 (10 + 10) SNo_0 (omega_SNo 10 H10o) (omega_SNo INTERVAL_EXP n20_omega) H10p.
rewrite <- add_SNo_0R 10 (omega_SNo 10 H10o) at 1.
exact add_SNo_Lt2 10 0 10 (omega_SNo 10 H10o) SNo_0 (omega_SNo 10 H10o) H10p.
Qed.

Theorem n80_lt_100 : RETAIN_EXP < MAX_EXP.
rewrite n100_eq_80_plus_20.
rewrite <- add_SNo_0R RETAIN_EXP (omega_SNo RETAIN_EXP n80_omega) at 1.
exact add_SNo_Lt2 RETAIN_EXP 0 INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) n20_pos.
Qed.

(** Floor bucket specification: b = floor(L / 20) iff 20b <= L < 20(b + 1) *)
Definition IsBucket20 : set -> set -> prop :=
  fun L b => b :e omega /\ b * INTERVAL_EXP <= L /\ L < (b + 1) * INTERVAL_EXP.

(** Constructive witness of the iter.metta:114-121 bucket-skip edge case:
    Build a ToolPaired history s of length 100 where index 19 is Assistant and
    index 20 is Tool (all other entries are User).
    1. window_trim 100 80 s drops 20 entries, yielding length 80 -> bucket 4 recorded.
    2. drop_leading_tools then sees Tool at new index 0 (old index 20), dropping it
       so final length is strictly < 80 (specifically 79).
    3. For EVERY subsequent length L < 100, its bucket b satisfies b <= 4, so
       cleanup_old_messages (guarded by b > 4 on line 115) CANNOT fire until L >= 100! *)
Definition witness_seq : set :=
  Seq MAX_EXP (fun i =>
    if i = INTERVAL_EXP then Msg RoleTool 0
    else Msg RoleAssistant 0).

Theorem witness_seq_valid : ValidSeq witness_seq.
exact ValidSeq_mk MAX_EXP n100_omega (fun i => if i = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0).
Qed.

Theorem witness_seq_ToolPaired : ToolPaired witness_seq.
let i. assume Hi Htool.
claim Hin : i :e MAX_EXP. { rewrite <- seq_len_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0). exact Hi. }
claim Hio : i :e omega. { exact nat_In_omega MAX_EXP n100_omega i Hin. }
claim Hi20 : i = INTERVAL_EXP.
{ apply xm (i = INTERVAL_EXP).
  - assume H : i = INTERVAL_EXP. exact H.
  - assume Hne : i <> INTERVAL_EXP.
    apply FalseE.
    claim Hat : seq_at witness_seq i = Msg RoleAssistant 0.
    { prove seq_at (Seq MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0)) i = Msg RoleAssistant 0.
      rewrite seq_at_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0) i Hin.
      exact If_i_0 (i = INTERVAL_EXP) (Msg RoleTool 0) (Msg RoleAssistant 0) Hne. }
    apply RoleAssistant_neq_Tool.
    rewrite <- msg_role_pair RoleAssistant 0.
    rewrite <- Hat. exact Htool. }
claim Hipos : 0 < i. { rewrite Hi20. exact n20_pos. }
apply nat_pos_pred i Hio Hipos. let k. assume Hk. apply Hk. assume Hko Hik.
claim Hkne : k <> INTERVAL_EXP.
{ assume Heq : k = INTERVAL_EXP.
  apply SNoLt_irref INTERVAL_EXP.
  rewrite <- Heq at 1. rewrite <- Hi20. rewrite Hik.
  rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
  exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1. }
claim Hkin : k :e MAX_EXP.
{ apply nat_SNoLt_In MAX_EXP n100_omega k Hko.
  apply SNoLt_tra k i MAX_EXP (omega_SNo k Hko) (omega_SNo i Hio) (omega_SNo MAX_EXP n100_omega).
  - rewrite Hik. rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
    exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
  - exact nat_In_SNoLt MAX_EXP n100_omega i Hin. }
claim Hatk : seq_at witness_seq k = Msg RoleAssistant 0.
{ prove seq_at (Seq MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0)) k = Msg RoleAssistant 0.
  rewrite seq_at_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0) k Hkin.
  exact If_i_0 (k = INTERVAL_EXP) (Msg RoleTool 0) (Msg RoleAssistant 0) Hkne. }
apply andI.
- exact Hipos.
- witness k. apply andI.
  + exact Hko.
  + apply andI.
    * exact Hik.
    * apply orIL. rewrite Hatk. exact msg_role_pair RoleAssistant 0.
Qed.

Theorem bucket_skip_witness :
  ValidSeq witness_seq /\ ToolPaired witness_seq /\
  seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) = RETAIN_EXP /\
  IsBucket20 (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) 4 /\
  seq_len (hygiene_step MAX_EXP RETAIN_EXP witness_seq) < RETAIN_EXP /\
  (forall L :e omega, L < MAX_EXP -> forall b, IsBucket20 L b -> ~(4 < b)).
claim Hwlen : seq_len witness_seq = MAX_EXP.
{ exact seq_len_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0). }
claim Htrim : window_trim MAX_EXP RETAIN_EXP witness_seq = seq_drop INTERVAL_EXP witness_seq.
{ prove (if MAX_EXP <= seq_len witness_seq then seq_drop (seq_len witness_seq + - RETAIN_EXP) witness_seq else witness_seq)
      = seq_drop INTERVAL_EXP witness_seq.
  rewrite Hwlen.
  rewrite If_i_1 (MAX_EXP <= MAX_EXP) (seq_drop (MAX_EXP + - RETAIN_EXP) witness_seq) witness_seq (SNoLe_ref MAX_EXP).
  claim Hsub : MAX_EXP + - RETAIN_EXP = INTERVAL_EXP.
  { rewrite n100_eq_80_plus_20.
    rewrite add_SNo_com RETAIN_EXP INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) (omega_SNo INTERVAL_EXP n20_omega).
    exact add_SNo_minus_R2 INTERVAL_EXP RETAIN_EXP (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega). }
  rewrite Hsub. reflexivity. }
claim Htrim_len : seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) = RETAIN_EXP.
{ rewrite Htrim.
  prove seq_len (Seq (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i))) = RETAIN_EXP.
  rewrite seq_len_mk (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i)).
  rewrite Hwlen. rewrite n100_eq_80_plus_20.
  exact add_SNo_minus_R2 RETAIN_EXP INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) (omega_SNo INTERVAL_EXP n20_omega). }
claim Htrim_v : ValidSeq (window_trim MAX_EXP RETAIN_EXP witness_seq).
{ prove seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega. rewrite Htrim_len. exact n80_omega. }
claim H80_pos : 0 < RETAIN_EXP.
{ claim H4o : 4 :e omega. { exact nat_p_omega 4 nat_4. }
  claim H4p : 0 < 4. { exact nat_In_SNoLt 4 H4o 0 In_0_4. }
  exact mul_SNo_pos_pos 4 INTERVAL_EXP (omega_SNo 4 H4o) (omega_SNo INTERVAL_EXP n20_omega) H4p n20_pos. }
claim H0_in_80 : 0 :e RETAIN_EXP. { exact nat_SNoLt_In RETAIN_EXP n80_omega 0 nat_0_omega H80_pos. }
claim H20_in_100 : INTERVAL_EXP :e MAX_EXP.
{ apply nat_SNoLt_In MAX_EXP n100_omega INTERVAL_EXP n20_omega.
  rewrite n100_eq_80_plus_20.
  rewrite <- add_SNo_0L INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega) at 1.
  exact add_SNo_Lt1 0 INTERVAL_EXP RETAIN_EXP SNo_0 (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega) H80_pos. }
claim Hhead_tool : msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) 0) = RoleTool.
{ rewrite Htrim.
  claim H0_sub : 0 :e seq_len witness_seq + - INTERVAL_EXP.
  { rewrite Hwlen. rewrite n100_eq_80_plus_20.
    rewrite add_SNo_minus_R2 RETAIN_EXP INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) (omega_SNo INTERVAL_EXP n20_omega).
    exact H0_in_80. }
  prove msg_role (seq_at (Seq (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i))) 0) = RoleTool.
  rewrite seq_at_mk (seq_len witness_seq + - INTERVAL_EXP) (fun i => seq_at witness_seq (INTERVAL_EXP + i)) 0 H0_sub.
  rewrite add_SNo_0R INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega).
  prove msg_role (seq_at (Seq MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0)) INTERVAL_EXP) = RoleTool.
  rewrite seq_at_mk MAX_EXP (fun j => if j = INTERVAL_EXP then Msg RoleTool 0 else Msg RoleAssistant 0) INTERVAL_EXP H20_in_100.
  claim Href20 : INTERVAL_EXP = INTERVAL_EXP. { reflexivity. }
  rewrite If_i_1 (INTERVAL_EXP = INTERVAL_EXP) (Msg RoleTool 0) (Msg RoleAssistant 0) Href20.
  exact msg_role_pair RoleTool 0. }
claim Hcut_pos : 0 < lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq).
{ claim Hspec : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) /\
    (forall j :e lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq), msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) j) = RoleTool) /\
    (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) = seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) \/
     msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))) <> RoleTool).
  { exact lead_tool_cut_spec (window_trim MAX_EXP RETAIN_EXP witness_seq) Htrim_v. }
  apply Hspec. assume Hc12 Hcor. apply Hc12. assume Hcin Hcall.
  claim Hco : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega.
  { exact nat_In_omega (ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq))) (omega_ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) Htrim_v) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hcin. }
  apply nat_SNoLe_cases 0 nat_0_omega (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco (nat_0_Le (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco).
  - assume H : 0 :e lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq).
    exact nat_In_SNoLt (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco 0 H.
  - assume H0 : 0 = lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq).
    apply FalseE.
    apply Hcor.
    + assume Heq : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) = seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq).
      apply SNoLt_irref 0.
      rewrite H0 at 2. rewrite Heq. rewrite Htrim_len. exact H80_pos.
    + assume Hne : msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))) <> RoleTool.
      apply Hne. rewrite <- H0. exact Hhead_tool. }
claim Hhyg_lt : seq_len (hygiene_step MAX_EXP RETAIN_EXP witness_seq) < RETAIN_EXP.
{ claim Hspec : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) /\
    (forall j :e lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq), msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) j) = RoleTool) /\
    (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) = seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) \/
     msg_role (seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))) <> RoleTool).
  { exact lead_tool_cut_spec (window_trim MAX_EXP RETAIN_EXP witness_seq) Htrim_v. }
  apply Hspec. assume Hc12 _. apply Hc12. assume Hcin _.
  claim Hco : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega.
  { exact nat_In_omega (ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq))) (omega_ordsucc (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) Htrim_v) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hcin. }
  claim Hcle : lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) <= RETAIN_EXP.
  { rewrite <- Htrim_len at 2. exact nat_In_ordsucc_Le (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq)) Htrim_v (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hcin. }
  claim Hsub_o : RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) :e omega.
  { exact nat_sub_omega (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco RETAIN_EXP n80_omega Hcle. }
  prove seq_len (Seq (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))
                     (fun i => seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) + i))) < RETAIN_EXP.
  rewrite seq_len_mk (seq_len (window_trim MAX_EXP RETAIN_EXP witness_seq) + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))
          (fun i => seq_at (window_trim MAX_EXP RETAIN_EXP witness_seq) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq) + i)).
  rewrite Htrim_len.
  rewrite <- SNo_add_sub_L RETAIN_EXP (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco) at 3.
  rewrite <- add_SNo_0L (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) (omega_SNo (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hsub_o) at 1.
  exact add_SNo_Lt1 0 (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq))
        SNo_0 (omega_SNo (RETAIN_EXP + - lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hsub_o)
        (omega_SNo (lead_tool_cut (window_trim MAX_EXP RETAIN_EXP witness_seq)) Hco) Hcut_pos. }
claim H5_eq : 4 + 1 = 5.
{ symmetry. exact ordsucc_eq_add_1 4 (nat_p_omega 4 nat_4). }
apply andI.
- apply andI.
  + apply andI.
    * apply andI.
      { apply andI.
        - exact witness_seq_valid.
        - exact witness_seq_ToolPaired. }
      { exact Htrim_len. }
    * rewrite Htrim_len.
      prove 4 :e omega /\ 4 * INTERVAL_EXP <= RETAIN_EXP /\ RETAIN_EXP < (4 + 1) * INTERVAL_EXP.
      rewrite H5_eq.
      apply and3I.
      { exact nat_p_omega 4 nat_4. }
      { exact SNoLe_ref RETAIN_EXP. }
      { exact n80_lt_100. }
  + exact Hhyg_lt.
- let L. assume HL Hlt100. let b. assume Hb H4b.
  apply Hb. assume Hbo1 Hltb. apply Hbo1. assume Hbo Hble.
  claim H5le : 5 <= b. { rewrite <- H5_eq. exact nat_SNoLt_S_Le 4 (nat_p_omega 4 nat_4) b Hbo H4b. }
  claim H100le : MAX_EXP <= b * INTERVAL_EXP.
  { prove 5 * INTERVAL_EXP <= b * INTERVAL_EXP.
    claim Hd_o : b + - 5 :e omega. { exact nat_sub_omega 5 (nat_p_omega 5 nat_5) b Hbo H5le. }
    claim Hdeq : b = 5 + (b + - 5). { symmetry. exact SNo_add_sub_L b 5 (omega_SNo b Hbo) (omega_SNo 5 (nat_p_omega 5 nat_5)). }
    claim Hprod_nn : 0 <= (b + - 5) * INTERVAL_EXP.
    { exact nat_0_Le ((b + - 5) * INTERVAL_EXP) (nat_mul_omega (b + - 5) Hd_o INTERVAL_EXP n20_omega). }
    rewrite Hdeq.
    rewrite mul_SNo_distrR 5 (b + - 5) INTERVAL_EXP (omega_SNo 5 (nat_p_omega 5 nat_5)) (omega_SNo (b + - 5) Hd_o) (omega_SNo INTERVAL_EXP n20_omega).
    rewrite <- add_SNo_0R (5 * INTERVAL_EXP) (omega_SNo MAX_EXP n100_omega) at 1.
    exact add_SNo_Le2 (5 * INTERVAL_EXP) 0 ((b + - 5) * INTERVAL_EXP) (omega_SNo MAX_EXP n100_omega) SNo_0
          (omega_SNo ((b + - 5) * INTERVAL_EXP) (nat_mul_omega (b + - 5) Hd_o INTERVAL_EXP n20_omega)) Hprod_nn. }
  claim H100leL : MAX_EXP <= L.
  { exact SNoLe_tra MAX_EXP (b * INTERVAL_EXP) L (omega_SNo MAX_EXP n100_omega) (omega_SNo (b * INTERVAL_EXP) (nat_mul_omega b Hbo INTERVAL_EXP n20_omega)) (omega_SNo L HL) H100le Hble. }
  exact SNoLt_irref L (SNoLtLe_tra L MAX_EXP L (omega_SNo L HL) (omega_SNo MAX_EXP n100_omega) (omega_SNo L HL) Hlt100 H100leL).
Qed.

(** Local firing lemma: whenever post-strip length L is strictly below RETAIN_EXP (80),
    its bucket is strictly below 4 while RETAIN_EXP has bucket 4.
    Group 5 below proves the full multi-step cycle consequence: recomputing the bucket
    after stripping causes an extra cleanup at L = 80 ONLY when k >= 1 orphans were
    stripped, producing a k-dependent 1-vs-2 cleanups/cycle asymmetry, whereas the
    original pre-strip reset fires uniformly 1 cleanup/cycle for all 0 <= k <= 20. *)
Theorem post_strip_bucket_fires_at_retain :
  forall L :e omega, L < RETAIN_EXP ->
  forall b, IsBucket20 L b -> b < 4 /\ IsBucket20 RETAIN_EXP 4.
let L. assume HL Hlt80. let b. assume Hb.
apply Hb. assume Hbo1 _. apply Hbo1. assume Hbo Hble.
claim H5_eq : 4 + 1 = 5.
{ symmetry. exact ordsucc_eq_add_1 4 (nat_p_omega 4 nat_4). }
apply andI.
- apply SNoLtLe_or b 4 (omega_SNo b Hbo) (omega_SNo 4 (nat_p_omega 4 nat_4)).
  + assume H : b < 4. exact H.
  + assume H4le : 4 <= b.
    apply FalseE.
    claim Hd_o : b + - 4 :e omega. { exact nat_sub_omega 4 (nat_p_omega 4 nat_4) b Hbo H4le. }
    claim Hdeq : b = 4 + (b + - 4). { symmetry. exact SNo_add_sub_L b 4 (omega_SNo b Hbo) (omega_SNo 4 (nat_p_omega 4 nat_4)). }
    claim Hprod_nn : 0 <= (b + - 4) * INTERVAL_EXP.
    { exact nat_0_Le ((b + - 4) * INTERVAL_EXP) (nat_mul_omega (b + - 4) Hd_o INTERVAL_EXP n20_omega). }
    claim H80le : RETAIN_EXP <= b * INTERVAL_EXP.
    { prove 4 * INTERVAL_EXP <= b * INTERVAL_EXP.
      rewrite Hdeq.
      rewrite mul_SNo_distrR 4 (b + - 4) INTERVAL_EXP (omega_SNo 4 (nat_p_omega 4 nat_4)) (omega_SNo (b + - 4) Hd_o) (omega_SNo INTERVAL_EXP n20_omega).
      rewrite <- add_SNo_0R (4 * INTERVAL_EXP) (omega_SNo RETAIN_EXP n80_omega) at 1.
      exact add_SNo_Le2 (4 * INTERVAL_EXP) 0 ((b + - 4) * INTERVAL_EXP) (omega_SNo RETAIN_EXP n80_omega) SNo_0
            (omega_SNo ((b + - 4) * INTERVAL_EXP) (nat_mul_omega (b + - 4) Hd_o INTERVAL_EXP n20_omega)) Hprod_nn. }
    claim H80leL : RETAIN_EXP <= L.
    { exact SNoLe_tra RETAIN_EXP (b * INTERVAL_EXP) L (omega_SNo RETAIN_EXP n80_omega) (omega_SNo (b * INTERVAL_EXP) (nat_mul_omega b Hbo INTERVAL_EXP n20_omega)) (omega_SNo L HL) H80le Hble. }
    exact SNoLt_irref L (SNoLtLe_tra L RETAIN_EXP L (omega_SNo L HL) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo L HL) Hlt80 H80leL).
- prove 4 :e omega /\ 4 * INTERVAL_EXP <= RETAIN_EXP /\ RETAIN_EXP < (4 + 1) * INTERVAL_EXP.
  rewrite H5_eq.
  apply and3I.
  + exact nat_p_omega 4 nat_4.
  + exact SNoLe_ref RETAIN_EXP.
  + exact n80_lt_100.
Qed.

(** ---- Theorem Group 5: Multi-Step Loop Cadence Comparison -----------------
    Models the exact multi-step Iter loop (iter.metta:113-128) with:
      - cleanup check: if bucket20 n > b then clean (count + 1, b := bucket20 n)
      - trim + strip:  if n >= 100 then trim to 80, strip k orphans -> 80 - k,
                       and reset bucket under either:
                         - PolicyPreStrip  (0): bucket := bucket20 80 = 4 (original)
                         - PolicyPostStrip (1): bucket := bucket20 (80 - k) (post-strip)
      - step append:   n := n + 1
    Proves:
      1. PolicyPreStrip yields a closed cycle of length 20 + k with UNIFORMLY 1
         cleanup per cycle for ALL 0 <= k <= 20.
      2. PolicyPostStrip yields 1 cleanup/cycle when k = 0, but 2 cleanups/cycle
         (at L = 80 and L = 100) for ALL 1 <= k <= 20 -> strict asymmetry (1 <> 2).
      3. Both bucketed policies delay cleanup until L = 100 when an uncleaned
         history of length L0 in [80, 100) is loaded with k = 0 at startup. *)

Theorem n2_eq_1_plus_1 : 2 = 1 + 1.
exact ordsucc_eq_add_1 1 nat_1_omega.
Qed.

Theorem n4_eq_3_plus_1 : 4 = 3 + 1.
exact ordsucc_eq_add_1 3 (nat_p_omega 3 nat_3).
Qed.

Theorem n5_eq_4_plus_1 : 5 = 4 + 1.
exact ordsucc_eq_add_1 4 (nat_p_omega 4 nat_4).
Qed.

Theorem n6_eq_5_plus_1 : 6 = 5 + 1.
exact ordsucc_eq_add_1 5 (nat_p_omega 5 nat_5).
Qed.

Theorem n60_omega : 3 * INTERVAL_EXP :e omega.
exact nat_mul_omega 3 (nat_p_omega 3 nat_3) INTERVAL_EXP n20_omega.
Qed.

Theorem n120_omega : 6 * INTERVAL_EXP :e omega.
exact nat_mul_omega 6 (nat_p_omega 6 nat_6) INTERVAL_EXP n20_omega.
Qed.

Theorem n80_eq_60_plus_20 : RETAIN_EXP = 3 * INTERVAL_EXP + INTERVAL_EXP.
prove 4 * INTERVAL_EXP = 3 * INTERVAL_EXP + INTERVAL_EXP.
rewrite <- mul_nat_mul_SNo 4 (nat_p_omega 4 nat_4) INTERVAL_EXP n20_omega.
prove mul_nat (ordsucc 3) INTERVAL_EXP = 3 * INTERVAL_EXP + INTERVAL_EXP.
rewrite mul_nat_SL 3 nat_3 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega).
rewrite add_nat_add_SNo (mul_nat 3 INTERVAL_EXP) (nat_p_omega (mul_nat 3 INTERVAL_EXP) (mul_nat_p 3 nat_3 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega))) INTERVAL_EXP n20_omega.
rewrite mul_nat_mul_SNo 3 (nat_p_omega 3 nat_3) INTERVAL_EXP n20_omega.
reflexivity.
Qed.

Theorem n120_eq_100_plus_20 : 6 * INTERVAL_EXP = MAX_EXP + INTERVAL_EXP.
rewrite <- mul_nat_mul_SNo 6 (nat_p_omega 6 nat_6) INTERVAL_EXP n20_omega.
prove mul_nat (ordsucc 5) INTERVAL_EXP = MAX_EXP + INTERVAL_EXP.
rewrite mul_nat_SL 5 nat_5 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega).
rewrite add_nat_add_SNo (mul_nat 5 INTERVAL_EXP) (nat_p_omega (mul_nat 5 INTERVAL_EXP) (mul_nat_p 5 nat_5 INTERVAL_EXP (omega_nat_p INTERVAL_EXP n20_omega))) INTERVAL_EXP n20_omega.
rewrite mul_nat_mul_SNo 5 (nat_p_omega 5 nat_5) INTERVAL_EXP n20_omega.
reflexivity.
Qed.

Theorem n100_lt_120 : MAX_EXP < 6 * INTERVAL_EXP.
rewrite n120_eq_100_plus_20.
rewrite <- add_SNo_0R MAX_EXP (omega_SNo MAX_EXP n100_omega) at 1.
exact add_SNo_Lt2 MAX_EXP 0 INTERVAL_EXP (omega_SNo MAX_EXP n100_omega) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) n20_pos.
Qed.

Theorem n19_omega : (10 + 9) :e omega.
exact nat_add_omega 10 (nat_p_omega 10 nat_10) 9 (nat_p_omega 9 nat_9).
Qed.

Theorem n20_eq_19_plus_1 : INTERVAL_EXP = (10 + 9) + 1.
prove 10 + 10 = (10 + 9) + 1.
claim H10 : 10 = 9 + 1. { exact ordsucc_eq_add_1 9 (nat_p_omega 9 nat_9). }
rewrite H10 at 2.
exact add_SNo_assoc 10 9 1 (omega_SNo 10 (nat_p_omega 10 nat_10)) (omega_SNo 9 (nat_p_omega 9 nat_9)) SNo_1.
Qed.

Theorem nat_mul_20_mono : forall a :e omega, forall b :e omega, a <= b -> a * INTERVAL_EXP <= b * INTERVAL_EXP.
let a. assume Ha. let b. assume Hb Hle.
claim Hd_o : b + - a :e omega. { exact nat_sub_omega a Ha b Hb Hle. }
claim Hdeq : b = a + (b + - a). { symmetry. exact SNo_add_sub_L b a (omega_SNo b Hb) (omega_SNo a Ha). }
claim Hprod_nn : 0 <= (b + - a) * INTERVAL_EXP.
{ exact nat_0_Le ((b + - a) * INTERVAL_EXP) (nat_mul_omega (b + - a) Hd_o INTERVAL_EXP n20_omega). }
rewrite Hdeq.
rewrite mul_SNo_distrR a (b + - a) INTERVAL_EXP (omega_SNo a Ha) (omega_SNo (b + - a) Hd_o) (omega_SNo INTERVAL_EXP n20_omega).
rewrite <- add_SNo_0R (a * INTERVAL_EXP) (omega_SNo (a * INTERVAL_EXP) (nat_mul_omega a Ha INTERVAL_EXP n20_omega)) at 1.
exact add_SNo_Le2 (a * INTERVAL_EXP) 0 ((b + - a) * INTERVAL_EXP)
      (omega_SNo (a * INTERVAL_EXP) (nat_mul_omega a Ha INTERVAL_EXP n20_omega)) SNo_0
      (omega_SNo ((b + - a) * INTERVAL_EXP) (nat_mul_omega (b + - a) Hd_o INTERVAL_EXP n20_omega)) Hprod_nn.
Qed.

Theorem IsBucket20_unique : forall L :e omega, forall b1 b2, IsBucket20 L b1 -> IsBucket20 L b2 -> b1 = b2.
let L. assume HL. let b1 b2. assume Hb1 Hb2.
apply Hb1. assume H1a H1lt. apply H1a. assume Hb1o H1le.
apply Hb2. assume H2a H2lt. apply H2a. assume Hb2o H2le.
apply ordinal_trichotomy_or_impred b1 b2 (nat_p_ordinal b1 (omega_nat_p b1 Hb1o)) (nat_p_ordinal b2 (omega_nat_p b2 Hb2o)).
- assume H12 : b1 :e b2.
  apply FalseE.
  claim Hle12 : b1 + 1 <= b2. { exact nat_SNoLt_S_Le b1 Hb1o b2 Hb2o (nat_In_SNoLt b2 Hb2o b1 H12). }
  claim Hm12 : (b1 + 1) * INTERVAL_EXP <= b2 * INTERVAL_EXP.
  { exact nat_mul_20_mono (b1 + 1) (nat_add_omega b1 Hb1o 1 nat_1_omega) b2 Hb2o Hle12. }
  claim HLle : (b1 + 1) * INTERVAL_EXP <= L.
  { exact SNoLe_tra ((b1 + 1) * INTERVAL_EXP) (b2 * INTERVAL_EXP) L
          (omega_SNo ((b1 + 1) * INTERVAL_EXP) (nat_mul_omega (b1 + 1) (nat_add_omega b1 Hb1o 1 nat_1_omega) INTERVAL_EXP n20_omega))
          (omega_SNo (b2 * INTERVAL_EXP) (nat_mul_omega b2 Hb2o INTERVAL_EXP n20_omega))
          (omega_SNo L HL) Hm12 H2le. }
  exact SNoLt_irref L (SNoLtLe_tra L ((b1 + 1) * INTERVAL_EXP) L
        (omega_SNo L HL)
        (omega_SNo ((b1 + 1) * INTERVAL_EXP) (nat_mul_omega (b1 + 1) (nat_add_omega b1 Hb1o 1 nat_1_omega) INTERVAL_EXP n20_omega))
        (omega_SNo L HL) H1lt HLle).
- assume Heq : b1 = b2. exact Heq.
- assume H21 : b2 :e b1.
  apply FalseE.
  claim Hle21 : b2 + 1 <= b1. { exact nat_SNoLt_S_Le b2 Hb2o b1 Hb1o (nat_In_SNoLt b1 Hb1o b2 H21). }
  claim Hm21 : (b2 + 1) * INTERVAL_EXP <= b1 * INTERVAL_EXP.
  { exact nat_mul_20_mono (b2 + 1) (nat_add_omega b2 Hb2o 1 nat_1_omega) b1 Hb1o Hle21. }
  claim HLle : (b2 + 1) * INTERVAL_EXP <= L.
  { exact SNoLe_tra ((b2 + 1) * INTERVAL_EXP) (b1 * INTERVAL_EXP) L
          (omega_SNo ((b2 + 1) * INTERVAL_EXP) (nat_mul_omega (b2 + 1) (nat_add_omega b2 Hb2o 1 nat_1_omega) INTERVAL_EXP n20_omega))
          (omega_SNo (b1 * INTERVAL_EXP) (nat_mul_omega b1 Hb1o INTERVAL_EXP n20_omega))
          (omega_SNo L HL) Hm21 H1le. }
  exact SNoLt_irref L (SNoLtLe_tra L ((b2 + 1) * INTERVAL_EXP) L
        (omega_SNo L HL)
        (omega_SNo ((b2 + 1) * INTERVAL_EXP) (nat_mul_omega (b2 + 1) (nat_add_omega b2 Hb2o 1 nat_1_omega) INTERVAL_EXP n20_omega))
        (omega_SNo L HL) H2lt HLle).
Qed.

Definition bucket20 : set -> set := fun L => Eps_i (fun b => IsBucket20 L b).

Theorem bucket20_eq : forall L :e omega, forall b, IsBucket20 L b -> bucket20 L = b.
let L. assume HL. let b. assume Hb.
claim Hex : exists x, IsBucket20 L x. { witness b. exact Hb. }
claim Hspec : IsBucket20 L (bucket20 L). { exact Eps_i_ex (fun x => IsBucket20 L x) Hex. }
exact IsBucket20_unique L HL (bucket20 L) b Hspec Hb.
Qed.

Theorem bucket20_60_to_79 : forall L :e omega, 3 * INTERVAL_EXP <= L -> L < RETAIN_EXP -> bucket20 L = 3.
let L. assume HL Hge Hlt.
apply bucket20_eq L HL 3.
prove 3 :e omega /\ 3 * INTERVAL_EXP <= L /\ L < (3 + 1) * INTERVAL_EXP.
rewrite <- n4_eq_3_plus_1.
apply and3I.
- exact nat_p_omega 3 nat_3.
- exact Hge.
- exact Hlt.
Qed.

Theorem bucket20_80_to_99 : forall L :e omega, RETAIN_EXP <= L -> L < MAX_EXP -> bucket20 L = 4.
let L. assume HL Hge Hlt.
apply bucket20_eq L HL 4.
prove 4 :e omega /\ 4 * INTERVAL_EXP <= L /\ L < (4 + 1) * INTERVAL_EXP.
rewrite <- n5_eq_4_plus_1.
apply and3I.
- exact nat_p_omega 4 nat_4.
- exact Hge.
- exact Hlt.
Qed.

Theorem bucket20_100 : bucket20 MAX_EXP = 5.
apply bucket20_eq MAX_EXP n100_omega 5.
prove 5 :e omega /\ 5 * INTERVAL_EXP <= MAX_EXP /\ MAX_EXP < (5 + 1) * INTERVAL_EXP.
rewrite <- n6_eq_5_plus_1.
apply and3I.
- exact nat_p_omega 5 nat_5.
- exact SNoLe_ref MAX_EXP.
- exact n100_lt_120.
Qed.

Definition PolicyPreStrip : set := 0.
Definition PolicyPostStrip : set := 1.

Theorem PolicyPostStrip_neq_PreStrip : PolicyPostStrip <> PolicyPreStrip.
assume Heq : 1 = 0.
apply SNoLt_irref 0.
rewrite <- Heq at 2.
exact SNoLt_0_1.
Qed.

Definition CadState : set -> set -> set -> set :=
  fun n b c => setsum n (setsum b c).
Definition cad_len : set -> set := fun st => proj0 st.
Definition cad_bucket : set -> set := fun st => proj0 (proj1 st).
Definition cad_count : set -> set := fun st => proj1 (proj1 st).

Theorem cad_len_mk : forall n b c, cad_len (CadState n b c) = n.
let n b c. exact proj0_pair_eq n (setsum b c).
Qed.

Theorem cad_bucket_mk : forall n b c, cad_bucket (CadState n b c) = b.
let n b c.
prove proj0 (proj1 (setsum n (setsum b c))) = b.
rewrite proj1_pair_eq n (setsum b c).
exact proj0_pair_eq b c.
Qed.

Theorem cad_count_mk : forall n b c, cad_count (CadState n b c) = c.
let n b c.
prove proj1 (proj1 (setsum n (setsum b c))) = c.
rewrite proj1_pair_eq n (setsum b c).
exact proj1_pair_eq b c.
Qed.

Definition cad_next_len : set -> set -> set :=
  fun k n => (if MAX_EXP <= n then RETAIN_EXP + - k else n) + 1.

Definition cad_next_bucket : set -> set -> set -> set -> set :=
  fun policy k n b =>
    if MAX_EXP <= n then
      (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
    else
      (if b < bucket20 n then bucket20 n else b).

Definition cad_next_count : set -> set -> set -> set :=
  fun n b c =>
    if b < bucket20 n then c + 1 else c.

Definition cad_step : set -> set -> set -> set :=
  fun policy k st =>
    CadState (cad_next_len k (cad_len st))
             (cad_next_bucket policy k (cad_len st) (cad_bucket st))
             (cad_next_count (cad_len st) (cad_bucket st) (cad_count st)).

Definition cad_run : set -> set -> set -> set -> set :=
  fun policy k st t => nat_primrec st (fun _ r => cad_step policy k r) t.

Theorem cad_run_0 : forall policy k st, cad_run policy k st 0 = st.
let policy k st.
exact nat_primrec_0 st (fun _ r => cad_step policy k r).
Qed.

Theorem cad_run_S : forall policy k st, forall t :e omega,
  cad_run policy k st (t + 1) = cad_step policy k (cad_run policy k st t).
let policy k st. let t. assume Ht.
rewrite <- ordsucc_eq_add_1 t Ht.
exact nat_primrec_S st (fun _ r => cad_step policy k r) t (omega_nat_p t Ht).
Qed.

Theorem cad_run_1 : forall policy k st, cad_run policy k st 1 = cad_step policy k st.
let policy k st.
claim H1 : 1 = 0 + 1. { symmetry. exact add_SNo_0L 1 SNo_1. }
rewrite H1.
rewrite cad_run_S policy k st 0 nat_0_omega.
rewrite cad_run_0 policy k st.
reflexivity.
Qed.

Theorem cad_run_add : forall policy k st, forall t1 :e omega, forall t2 :e omega,
  cad_run policy k st (t1 + t2) = cad_run policy k (cad_run policy k st t1) t2.
let policy k st. let t1. assume Ht1. let t2. assume Ht2.
apply nat_ind (fun m => cad_run policy k st (t1 + m) = cad_run policy k (cad_run policy k st t1) m).
- prove cad_run policy k st (t1 + 0) = cad_run policy k (cad_run policy k st t1) 0.
  rewrite add_SNo_0R t1 (omega_SNo t1 Ht1).
  symmetry. exact cad_run_0 policy k (cad_run policy k st t1).
- let m. assume Hm IH.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  prove cad_run policy k st (t1 + ordsucc m) = cad_run policy k (cad_run policy k st t1) (ordsucc m).
  rewrite ordsucc_eq_add_1 m Hmo.
  rewrite add_SNo_assoc t1 m 1 (omega_SNo t1 Ht1) (omega_SNo m Hmo) SNo_1.
  rewrite cad_run_S policy k st (t1 + m) (nat_add_omega t1 Ht1 m Hmo).
  rewrite cad_run_S policy k (cad_run policy k st t1) m Hmo.
  rewrite IH. reflexivity.
- exact omega_nat_p t2 Ht2.
Qed.

Theorem cad_step_silent : forall policy k,
  forall L :e omega, forall b c,
  L < MAX_EXP -> ~(b < bucket20 L) ->
  cad_step policy k (CadState L b c) = CadState (L + 1) b c.
let policy k. let L. assume HL. let b c. assume Hlt Hnb.
claim Hnle : ~(MAX_EXP <= L).
{ assume Hle : MAX_EXP <= L.
  exact SNoLt_irref L (SNoLtLe_tra L MAX_EXP L (omega_SNo L HL) (omega_SNo MAX_EXP n100_omega) (omega_SNo L HL) Hlt Hle). }
prove CadState (cad_next_len k (cad_len (CadState L b c)))
               (cad_next_bucket policy k (cad_len (CadState L b c)) (cad_bucket (CadState L b c)))
               (cad_next_count (cad_len (CadState L b c)) (cad_bucket (CadState L b c)) (cad_count (CadState L b c)))
    = CadState (L + 1) b c.
rewrite cad_len_mk L b c.
rewrite cad_bucket_mk L b c.
rewrite cad_count_mk L b c.
claim Hnl : cad_next_len k L = L + 1.
{ prove (if MAX_EXP <= L then RETAIN_EXP + - k else L) + 1 = L + 1.
  rewrite If_i_0 (MAX_EXP <= L) (RETAIN_EXP + - k) L Hnle. reflexivity. }
claim Hnbk : cad_next_bucket policy k L b = b.
{ prove (if MAX_EXP <= L then
           (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
         else
           (if b < bucket20 L then bucket20 L else b)) = b.
  rewrite If_i_0 (MAX_EXP <= L)
          (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
          (if b < bucket20 L then bucket20 L else b) Hnle.
  exact If_i_0 (b < bucket20 L) (bucket20 L) b Hnb. }
claim Hnc : cad_next_count L b c = c.
{ exact If_i_0 (b < bucket20 L) (c + 1) c Hnb. }
rewrite Hnl. rewrite Hnbk. rewrite Hnc. reflexivity.
Qed.

Theorem cad_run_silent_range : forall policy k,
  forall L0 :e omega, forall b c, forall t :e omega,
  (forall j :e t, L0 + j < MAX_EXP /\ ~(b < bucket20 (L0 + j))) ->
  cad_run policy k (CadState L0 b c) t = CadState (L0 + t) b c.
let policy k. let L0. assume HL0. let b c. let t. assume Ht.
apply nat_ind (fun m =>
  (forall j :e m, L0 + j < MAX_EXP /\ ~(b < bucket20 (L0 + j))) ->
  cad_run policy k (CadState L0 b c) m = CadState (L0 + m) b c).
- assume _.
  prove cad_run policy k (CadState L0 b c) 0 = CadState (L0 + 0) b c.
  rewrite cad_run_0 policy k (CadState L0 b c).
  rewrite add_SNo_0R L0 (omega_SNo L0 HL0). reflexivity.
- let m. assume Hm IH Hstep.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  claim Hprev : forall j :e m, L0 + j < MAX_EXP /\ ~(b < bucket20 (L0 + j)).
  { let j. assume Hj. exact Hstep j (ordsuccI1 m j Hj). }
  claim Hm_cond : L0 + m < MAX_EXP /\ ~(b < bucket20 (L0 + m)).
  { exact Hstep m (ordsuccI2 m). }
  prove cad_run policy k (CadState L0 b c) (ordsucc m) = CadState (L0 + ordsucc m) b c.
  rewrite ordsucc_eq_add_1 m Hmo.
  rewrite cad_run_S policy k (CadState L0 b c) m Hmo.
  rewrite IH Hprev.
  apply Hm_cond. assume Hlt Hnb.
  rewrite cad_step_silent policy k (L0 + m) (nat_add_omega L0 HL0 m Hmo) b c Hlt Hnb.
  rewrite add_SNo_assoc L0 m 1 (omega_SNo L0 HL0) (omega_SNo m Hmo) SNo_1.
  reflexivity.
- exact omega_nat_p t Ht.
Qed.

Theorem cad_step_at_100 : forall policy k c,
  cad_step policy k (CadState MAX_EXP 4 c) =
  CadState ((RETAIN_EXP + - k) + 1)
           (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
           (c + 1).
let policy k c.
prove CadState (cad_next_len k (cad_len (CadState MAX_EXP 4 c)))
               (cad_next_bucket policy k (cad_len (CadState MAX_EXP 4 c)) (cad_bucket (CadState MAX_EXP 4 c)))
               (cad_next_count (cad_len (CadState MAX_EXP 4 c)) (cad_bucket (CadState MAX_EXP 4 c)) (cad_count (CadState MAX_EXP 4 c)))
    = CadState ((RETAIN_EXP + - k) + 1)
               (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
               (c + 1).
rewrite cad_len_mk MAX_EXP 4 c.
rewrite cad_bucket_mk MAX_EXP 4 c.
rewrite cad_count_mk MAX_EXP 4 c.
claim H45 : 4 < bucket20 MAX_EXP.
{ rewrite bucket20_100. exact nat_In_SNoLt 5 (nat_p_omega 5 nat_5) 4 In_4_5. }
claim Hnl : cad_next_len k MAX_EXP = (RETAIN_EXP + - k) + 1.
{ prove (if MAX_EXP <= MAX_EXP then RETAIN_EXP + - k else MAX_EXP) + 1 = (RETAIN_EXP + - k) + 1.
  rewrite If_i_1 (MAX_EXP <= MAX_EXP) (RETAIN_EXP + - k) MAX_EXP (SNoLe_ref MAX_EXP). reflexivity. }
claim Hnbk : cad_next_bucket policy k MAX_EXP 4 =
  (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k)).
{ exact If_i_1 (MAX_EXP <= MAX_EXP)
        (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
        (if 4 < bucket20 MAX_EXP then bucket20 MAX_EXP else 4) (SNoLe_ref MAX_EXP). }
claim Hnc : cad_next_count MAX_EXP 4 c = c + 1.
{ exact If_i_1 (4 < bucket20 MAX_EXP) (c + 1) c H45. }
rewrite Hnl. rewrite Hnbk. rewrite Hnc. reflexivity.
Qed.

Theorem cad_step_at_80_from_3 : forall policy k c,
  cad_step policy k (CadState RETAIN_EXP 3 c) = CadState (RETAIN_EXP + 1) 4 (c + 1).
let policy k c.
prove CadState (cad_next_len k (cad_len (CadState RETAIN_EXP 3 c)))
               (cad_next_bucket policy k (cad_len (CadState RETAIN_EXP 3 c)) (cad_bucket (CadState RETAIN_EXP 3 c)))
               (cad_next_count (cad_len (CadState RETAIN_EXP 3 c)) (cad_bucket (CadState RETAIN_EXP 3 c)) (cad_count (CadState RETAIN_EXP 3 c)))
    = CadState (RETAIN_EXP + 1) 4 (c + 1).
rewrite cad_len_mk RETAIN_EXP 3 c.
rewrite cad_bucket_mk RETAIN_EXP 3 c.
rewrite cad_count_mk RETAIN_EXP 3 c.
claim Hnle : ~(MAX_EXP <= RETAIN_EXP).
{ assume Hle : MAX_EXP <= RETAIN_EXP.
  exact SNoLt_irref RETAIN_EXP (SNoLtLe_tra RETAIN_EXP MAX_EXP RETAIN_EXP (omega_SNo RETAIN_EXP n80_omega) (omega_SNo MAX_EXP n100_omega) (omega_SNo RETAIN_EXP n80_omega) n80_lt_100 Hle). }
claim Hb80 : bucket20 RETAIN_EXP = 4.
{ exact bucket20_80_to_99 RETAIN_EXP n80_omega (SNoLe_ref RETAIN_EXP) n80_lt_100. }
claim H34 : 3 < bucket20 RETAIN_EXP.
{ rewrite Hb80. exact nat_In_SNoLt 4 (nat_p_omega 4 nat_4) 3 In_3_4. }
claim Hnl : cad_next_len k RETAIN_EXP = RETAIN_EXP + 1.
{ prove (if MAX_EXP <= RETAIN_EXP then RETAIN_EXP + - k else RETAIN_EXP) + 1 = RETAIN_EXP + 1.
  rewrite If_i_0 (MAX_EXP <= RETAIN_EXP) (RETAIN_EXP + - k) RETAIN_EXP Hnle. reflexivity. }
claim Hnbk : cad_next_bucket policy k RETAIN_EXP 3 = 4.
{ prove (if MAX_EXP <= RETAIN_EXP then
           (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
         else
           (if 3 < bucket20 RETAIN_EXP then bucket20 RETAIN_EXP else 3)) = 4.
  rewrite If_i_0 (MAX_EXP <= RETAIN_EXP)
          (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
          (if 3 < bucket20 RETAIN_EXP then bucket20 RETAIN_EXP else 3) Hnle.
  rewrite If_i_1 (3 < bucket20 RETAIN_EXP) (bucket20 RETAIN_EXP) 3 H34.
  exact Hb80. }
claim Hnc : cad_next_count RETAIN_EXP 3 c = c + 1.
{ exact If_i_1 (3 < bucket20 RETAIN_EXP) (c + 1) c H34. }
rewrite Hnl. rewrite Hnbk. rewrite Hnc. reflexivity.
Qed.

(** Helper: for 0 <= k <= 20, 60 <= 80 - k and (80 - k) + 1 + (19 + k) = 100. *)
Theorem retain_sub_ge_60 : forall k :e omega, k <= INTERVAL_EXP -> 3 * INTERVAL_EXP <= RETAIN_EXP + - k.
let k. assume Hk Hkle.
claim Hsub_o : INTERVAL_EXP + - k :e omega. { exact nat_sub_omega k Hk INTERVAL_EXP n20_omega Hkle. }
claim Hk80 : k <= RETAIN_EXP.
{ apply SNoLe_tra k INTERVAL_EXP RETAIN_EXP (omega_SNo k Hk) (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega) Hkle.
  rewrite n80_eq_60_plus_20.
  rewrite <- add_SNo_0L INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega) at 1.
  exact add_SNo_Le1 0 INTERVAL_EXP (3 * INTERVAL_EXP) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo (3 * INTERVAL_EXP) n60_omega) (nat_0_Le (3 * INTERVAL_EXP) n60_omega). }
claim Heq : RETAIN_EXP + - k = 3 * INTERVAL_EXP + (INTERVAL_EXP + - k).
{ rewrite n80_eq_60_plus_20.
  symmetry.
  exact add_SNo_assoc (3 * INTERVAL_EXP) INTERVAL_EXP (- k)
        (omega_SNo (3 * INTERVAL_EXP) n60_omega) (omega_SNo INTERVAL_EXP n20_omega) (SNo_minus_SNo k (omega_SNo k Hk)). }
rewrite Heq.
rewrite <- add_SNo_0R (3 * INTERVAL_EXP) (omega_SNo (3 * INTERVAL_EXP) n60_omega) at 1.
exact add_SNo_Le2 (3 * INTERVAL_EXP) 0 (INTERVAL_EXP + - k)
      (omega_SNo (3 * INTERVAL_EXP) n60_omega) SNo_0 (omega_SNo (INTERVAL_EXP + - k) Hsub_o) (nat_0_Le (INTERVAL_EXP + - k) Hsub_o).
Qed.

Theorem cycle_len_sum_100 : forall k :e omega, k <= INTERVAL_EXP ->
  ((RETAIN_EXP + - k) + 1) + ((10 + 9) + k) = MAX_EXP.
let k. assume Hk Hkle.
claim Hk80 : k <= RETAIN_EXP.
{ apply SNoLe_tra k INTERVAL_EXP RETAIN_EXP (omega_SNo k Hk) (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega) Hkle.
  rewrite n80_eq_60_plus_20.
  rewrite <- add_SNo_0L INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega) at 1.
  exact add_SNo_Le1 0 INTERVAL_EXP (3 * INTERVAL_EXP) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo (3 * INTERVAL_EXP) n60_omega) (nat_0_Le (3 * INTERVAL_EXP) n60_omega). }
claim Hsub_o : RETAIN_EXP + - k :e omega. { exact nat_sub_omega k Hk RETAIN_EXP n80_omega Hk80. }
claim HS80k : SNo (RETAIN_EXP + - k). { exact omega_SNo (RETAIN_EXP + - k) Hsub_o. }
claim HS19 : SNo (10 + 9). { exact omega_SNo (10 + 9) n19_omega. }
claim HSk : SNo k. { exact omega_SNo k Hk. }
rewrite add_SNo_com (10 + 9) k HS19 HSk.
rewrite add_SNo_assoc ((RETAIN_EXP + - k) + 1) k (10 + 9) (SNo_add_SNo (RETAIN_EXP + - k) 1 HS80k SNo_1) HSk HS19.
rewrite <- add_SNo_assoc (RETAIN_EXP + - k) 1 k HS80k SNo_1 HSk.
rewrite add_SNo_com 1 k SNo_1 HSk.
rewrite add_SNo_assoc (RETAIN_EXP + - k) k 1 HS80k HSk SNo_1.
rewrite add_SNo_com (RETAIN_EXP + - k) k HS80k HSk.
rewrite SNo_add_sub_L RETAIN_EXP k (omega_SNo RETAIN_EXP n80_omega) HSk.
rewrite <- add_SNo_assoc RETAIN_EXP 1 (10 + 9) (omega_SNo RETAIN_EXP n80_omega) SNo_1 HS19.
rewrite add_SNo_com 1 (10 + 9) SNo_1 HS19.
rewrite <- n20_eq_19_plus_1.
symmetry. exact n100_eq_80_plus_20.
Qed.

(** MAIN CADENCE THEOREM 1 (Original pre-strip bucket):
    For EVERY orphan strip count 0 <= k <= 20, the original pre-strip loop completes
    a closed cycle of length 20 + k with UNIFORMLY 1 cleanup per cycle (c -> c + 1). *)
Theorem original_full_cycle_uniform_1 :
  forall k :e omega, k <= INTERVAL_EXP -> forall c :e omega,
  cad_run PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) (INTERVAL_EXP + k) =
  CadState ((RETAIN_EXP + - k) + 1) 4 (c + 1).
let k. assume Hk Hkle. let c. assume Hc.
claim Hk80 : k <= RETAIN_EXP.
{ apply SNoLe_tra k INTERVAL_EXP RETAIN_EXP (omega_SNo k Hk) (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega) Hkle.
  rewrite n80_eq_60_plus_20.
  rewrite <- add_SNo_0L INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega) at 1.
  exact add_SNo_Le1 0 INTERVAL_EXP (3 * INTERVAL_EXP) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo (3 * INTERVAL_EXP) n60_omega) (nat_0_Le (3 * INTERVAL_EXP) n60_omega). }
claim Hsub_o : RETAIN_EXP + - k :e omega. { exact nat_sub_omega k Hk RETAIN_EXP n80_omega Hk80. }
claim HL0_o : (RETAIN_EXP + - k) + 1 :e omega. { exact nat_add_omega (RETAIN_EXP + - k) Hsub_o 1 nat_1_omega. }
claim Hts_o : (10 + 9) + k :e omega. { exact nat_add_omega (10 + 9) n19_omega k Hk. }
claim Htot_eq : INTERVAL_EXP + k = ((10 + 9) + k) + 1.
{ rewrite n20_eq_19_plus_1.
  rewrite <- add_SNo_assoc (10 + 9) 1 k (omega_SNo (10 + 9) n19_omega) SNo_1 (omega_SNo k Hk).
  rewrite add_SNo_com 1 k SNo_1 (omega_SNo k Hk).
  exact add_SNo_assoc (10 + 9) k 1 (omega_SNo (10 + 9) n19_omega) (omega_SNo k Hk) SNo_1. }
rewrite Htot_eq.
rewrite cad_run_add PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) ((10 + 9) + k) Hts_o 1 nat_1_omega.
claim Hsil : cad_run PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) ((10 + 9) + k) = CadState MAX_EXP 4 c.
{ rewrite <- cycle_len_sum_100 k Hk Hkle.
  apply cad_run_silent_range PolicyPreStrip k ((RETAIN_EXP + - k) + 1) HL0_o 4 c ((10 + 9) + k) Hts_o.
  let j. assume Hj.
  claim Hjo : j :e omega. { exact nat_In_omega ((10 + 9) + k) Hts_o j Hj. }
  claim HL_o : ((RETAIN_EXP + - k) + 1) + j :e omega. { exact nat_add_omega ((RETAIN_EXP + - k) + 1) HL0_o j Hjo. }
  claim HL_lt : ((RETAIN_EXP + - k) + 1) + j < MAX_EXP.
  { rewrite <- cycle_len_sum_100 k Hk Hkle.
    exact add_SNo_Lt2 ((RETAIN_EXP + - k) + 1) j ((10 + 9) + k)
          (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) (omega_SNo j Hjo) (omega_SNo ((10 + 9) + k) Hts_o)
          (nat_In_SNoLt ((10 + 9) + k) Hts_o j Hj). }
  claim HL_ge60 : 3 * INTERVAL_EXP <= ((RETAIN_EXP + - k) + 1) + j.
  { apply SNoLe_tra (3 * INTERVAL_EXP) (RETAIN_EXP + - k) (((RETAIN_EXP + - k) + 1) + j)
          (omega_SNo (3 * INTERVAL_EXP) n60_omega) (omega_SNo (RETAIN_EXP + - k) Hsub_o) (omega_SNo (((RETAIN_EXP + - k) + 1) + j) HL_o)
          (retain_sub_ge_60 k Hk Hkle).
    apply SNoLe_tra (RETAIN_EXP + - k) ((RETAIN_EXP + - k) + 1) (((RETAIN_EXP + - k) + 1) + j)
          (omega_SNo (RETAIN_EXP + - k) Hsub_o) (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) (omega_SNo (((RETAIN_EXP + - k) + 1) + j) HL_o).
    - rewrite <- add_SNo_0R (RETAIN_EXP + - k) (omega_SNo (RETAIN_EXP + - k) Hsub_o) at 1.
      exact add_SNo_Le2 (RETAIN_EXP + - k) 0 1 (omega_SNo (RETAIN_EXP + - k) Hsub_o) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
    - rewrite <- add_SNo_0R ((RETAIN_EXP + - k) + 1) (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) at 1.
      exact add_SNo_Le2 ((RETAIN_EXP + - k) + 1) 0 j (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) SNo_0 (omega_SNo j Hjo) (nat_0_Le j Hjo). }
  apply andI.
  - exact HL_lt.
  - apply SNoLtLe_or (((RETAIN_EXP + - k) + 1) + j) RETAIN_EXP (omega_SNo (((RETAIN_EXP + - k) + 1) + j) HL_o) (omega_SNo RETAIN_EXP n80_omega).
    + assume Hlt80 : ((RETAIN_EXP + - k) + 1) + j < RETAIN_EXP.
      rewrite bucket20_60_to_79 (((RETAIN_EXP + - k) + 1) + j) HL_o HL_ge60 Hlt80.
      assume H43 : 4 < 3.
      exact SNoLt_irref 3 (SNoLt_tra 3 4 3 (omega_SNo 3 (nat_p_omega 3 nat_3)) (omega_SNo 4 (nat_p_omega 4 nat_4)) (omega_SNo 3 (nat_p_omega 3 nat_3))
            (nat_In_SNoLt 4 (nat_p_omega 4 nat_4) 3 In_3_4) H43).
    + assume Hge80 : RETAIN_EXP <= ((RETAIN_EXP + - k) + 1) + j.
      rewrite bucket20_80_to_99 (((RETAIN_EXP + - k) + 1) + j) HL_o Hge80 HL_lt.
      exact SNoLt_irref 4. }
rewrite Hsil.
rewrite cad_run_1 PolicyPreStrip k (CadState MAX_EXP 4 c).
rewrite cad_step_at_100 PolicyPreStrip k c.
claim Href : PolicyPreStrip = PolicyPreStrip. { reflexivity. }
rewrite If_i_1 (PolicyPreStrip = PolicyPreStrip) (bucket20 RETAIN_EXP) (bucket20 (RETAIN_EXP + - k)) Href.
rewrite bucket20_80_to_99 RETAIN_EXP n80_omega (SNoLe_ref RETAIN_EXP) n80_lt_100.
reflexivity.
Qed.

(** MAIN CADENCE THEOREM 2 (Post-strip bucket when k = 0):
    When no leading tool messages are stripped (k = 0), post-strip completes its
    20-step closed cycle with 1 cleanup per cycle (c -> c + 1). *)
Theorem post_strip_full_cycle_k0_is_1 :
  forall c :e omega,
  cad_run PolicyPostStrip 0 (CadState (RETAIN_EXP + 1) 4 c) INTERVAL_EXP =
  CadState (RETAIN_EXP + 1) 4 (c + 1).
let c. assume Hc.
claim HL0_o : RETAIN_EXP + 1 :e omega. { exact nat_add_omega RETAIN_EXP n80_omega 1 nat_1_omega. }
claim Hsum : (RETAIN_EXP + 1) + (10 + 9) = MAX_EXP.
{ rewrite <- add_SNo_assoc RETAIN_EXP 1 (10 + 9) (omega_SNo RETAIN_EXP n80_omega) SNo_1 (omega_SNo (10 + 9) n19_omega).
  rewrite add_SNo_com 1 (10 + 9) SNo_1 (omega_SNo (10 + 9) n19_omega).
  rewrite <- n20_eq_19_plus_1.
  symmetry. exact n100_eq_80_plus_20. }
rewrite n20_eq_19_plus_1.
rewrite cad_run_add PolicyPostStrip 0 (CadState (RETAIN_EXP + 1) 4 c) (10 + 9) n19_omega 1 nat_1_omega.
claim Hsil : cad_run PolicyPostStrip 0 (CadState (RETAIN_EXP + 1) 4 c) (10 + 9) = CadState MAX_EXP 4 c.
{ rewrite <- Hsum.
  apply cad_run_silent_range PolicyPostStrip 0 (RETAIN_EXP + 1) HL0_o 4 c (10 + 9) n19_omega.
  let j. assume Hj.
  claim Hjo : j :e omega. { exact nat_In_omega (10 + 9) n19_omega j Hj. }
  claim HL_o : (RETAIN_EXP + 1) + j :e omega. { exact nat_add_omega (RETAIN_EXP + 1) HL0_o j Hjo. }
  claim HL_lt : (RETAIN_EXP + 1) + j < MAX_EXP.
  { rewrite <- Hsum.
    exact add_SNo_Lt2 (RETAIN_EXP + 1) j (10 + 9) (omega_SNo (RETAIN_EXP + 1) HL0_o) (omega_SNo j Hjo) (omega_SNo (10 + 9) n19_omega)
          (nat_In_SNoLt (10 + 9) n19_omega j Hj). }
  claim HL_ge80 : RETAIN_EXP <= (RETAIN_EXP + 1) + j.
  { apply SNoLe_tra RETAIN_EXP (RETAIN_EXP + 1) ((RETAIN_EXP + 1) + j) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo (RETAIN_EXP + 1) HL0_o) (omega_SNo ((RETAIN_EXP + 1) + j) HL_o).
    - rewrite <- add_SNo_0R RETAIN_EXP (omega_SNo RETAIN_EXP n80_omega) at 1.
      exact add_SNo_Le2 RETAIN_EXP 0 1 (omega_SNo RETAIN_EXP n80_omega) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
    - rewrite <- add_SNo_0R (RETAIN_EXP + 1) (omega_SNo (RETAIN_EXP + 1) HL0_o) at 1.
      exact add_SNo_Le2 (RETAIN_EXP + 1) 0 j (omega_SNo (RETAIN_EXP + 1) HL0_o) SNo_0 (omega_SNo j Hjo) (nat_0_Le j Hjo). }
  apply andI.
  - exact HL_lt.
  - rewrite bucket20_80_to_99 ((RETAIN_EXP + 1) + j) HL_o HL_ge80 HL_lt.
    exact SNoLt_irref 4. }
rewrite Hsil.
rewrite cad_run_1 PolicyPostStrip 0 (CadState MAX_EXP 4 c).
rewrite cad_step_at_100 PolicyPostStrip 0 c.
rewrite If_i_0 (PolicyPostStrip = PolicyPreStrip) (bucket20 RETAIN_EXP) (bucket20 (RETAIN_EXP + - 0)) PolicyPostStrip_neq_PreStrip.
rewrite minus_SNo_0.
rewrite add_SNo_0R RETAIN_EXP (omega_SNo RETAIN_EXP n80_omega).
rewrite bucket20_80_to_99 RETAIN_EXP n80_omega (SNoLe_ref RETAIN_EXP) n80_lt_100.
reflexivity.
Qed.

(** MAIN CADENCE THEOREM 3 (Post-strip bucket when 1 <= k <= 20):
    Whenever 1 <= k <= 20 orphaned tool messages are stripped on trim, post-strip
    sets bucket = 3, firing an EXTRA cleanup at L = 80 AND a second cleanup at L = 100
    -> EXACTLY 2 cleanups per closed cycle (c -> c + 2)! *)
Theorem post_strip_full_cycle_kpos_is_2 :
  forall k :e omega, 1 <= k -> k <= INTERVAL_EXP -> forall c :e omega,
  cad_run PolicyPostStrip k (CadState ((RETAIN_EXP + - k) + 1) 3 c) (INTERVAL_EXP + k) =
  CadState ((RETAIN_EXP + - k) + 1) 3 (c + 2).
let k. assume Hk H1k Hkle. let c. assume Hc.
claim Hk80 : k <= RETAIN_EXP.
{ apply SNoLe_tra k INTERVAL_EXP RETAIN_EXP (omega_SNo k Hk) (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega) Hkle.
  rewrite n80_eq_60_plus_20.
  rewrite <- add_SNo_0L INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega) at 1.
  exact add_SNo_Le1 0 INTERVAL_EXP (3 * INTERVAL_EXP) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo (3 * INTERVAL_EXP) n60_omega) (nat_0_Le (3 * INTERVAL_EXP) n60_omega). }
claim Hsub_o : RETAIN_EXP + - k :e omega. { exact nat_sub_omega k Hk RETAIN_EXP n80_omega Hk80. }
claim HL0_o : (RETAIN_EXP + - k) + 1 :e omega. { exact nat_add_omega (RETAIN_EXP + - k) Hsub_o 1 nat_1_omega. }
claim Hkm1_o : k + - 1 :e omega. { exact nat_sub_omega 1 nat_1_omega k Hk H1k. }
claim Hc1_o : c + 1 :e omega. { exact nat_add_omega c Hc 1 nat_1_omega. }
claim H81_o : RETAIN_EXP + 1 :e omega. { exact nat_add_omega RETAIN_EXP n80_omega 1 nat_1_omega. }
claim Hk_pos : 0 < k.
{ exact SNoLtLe_tra 0 1 k SNo_0 SNo_1 (omega_SNo k Hk) SNoLt_0_1 H1k. }
claim Hsub_lt80 : RETAIN_EXP + - k < RETAIN_EXP.
{ rewrite <- SNo_add_sub_L RETAIN_EXP k (omega_SNo RETAIN_EXP n80_omega) (omega_SNo k Hk) at 2.
  rewrite <- add_SNo_0L (RETAIN_EXP + - k) (omega_SNo (RETAIN_EXP + - k) Hsub_o) at 1.
  exact add_SNo_Lt1 0 (RETAIN_EXP + - k) k SNo_0 (omega_SNo (RETAIN_EXP + - k) Hsub_o) (omega_SNo k Hk) Hk_pos. }
claim Hsub_ge60 : 3 * INTERVAL_EXP <= RETAIN_EXP + - k. { exact retain_sub_ge_60 k Hk Hkle. }
claim Hp1_sum : ((RETAIN_EXP + - k) + 1) + (k + - 1) = RETAIN_EXP.
{ rewrite <- add_SNo_assoc (RETAIN_EXP + - k) 1 (k + - 1) (omega_SNo (RETAIN_EXP + - k) Hsub_o) SNo_1 (omega_SNo (k + - 1) Hkm1_o).
  rewrite SNo_add_sub_L k 1 (omega_SNo k Hk) SNo_1.
  rewrite add_SNo_com (RETAIN_EXP + - k) k (omega_SNo (RETAIN_EXP + - k) Hsub_o) (omega_SNo k Hk).
  exact SNo_add_sub_L RETAIN_EXP k (omega_SNo RETAIN_EXP n80_omega) (omega_SNo k Hk). }
claim Hp3_sum : (RETAIN_EXP + 1) + (10 + 9) = MAX_EXP.
{ rewrite <- add_SNo_assoc RETAIN_EXP 1 (10 + 9) (omega_SNo RETAIN_EXP n80_omega) SNo_1 (omega_SNo (10 + 9) n19_omega).
  rewrite add_SNo_com 1 (10 + 9) SNo_1 (omega_SNo (10 + 9) n19_omega).
  rewrite <- n20_eq_19_plus_1.
  symmetry. exact n100_eq_80_plus_20. }
claim Htot : INTERVAL_EXP + k = ((k + - 1) + 1) + ((10 + 9) + 1).
{ rewrite add_SNo_com INTERVAL_EXP k (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo k Hk).
  rewrite <- n20_eq_19_plus_1.
  rewrite add_SNo_com (k + - 1) 1 (omega_SNo (k + - 1) Hkm1_o) SNo_1.
  rewrite SNo_add_sub_L k 1 (omega_SNo k Hk) SNo_1.
  reflexivity. }
rewrite Htot.
rewrite cad_run_add PolicyPostStrip k (CadState ((RETAIN_EXP + - k) + 1) 3 c) ((k + - 1) + 1) (nat_add_omega (k + - 1) Hkm1_o 1 nat_1_omega) ((10 + 9) + 1) (nat_add_omega (10 + 9) n19_omega 1 nat_1_omega).
rewrite cad_run_add PolicyPostStrip k (CadState ((RETAIN_EXP + - k) + 1) 3 c) (k + - 1) Hkm1_o 1 nat_1_omega.
claim Hphase1 : cad_run PolicyPostStrip k (CadState ((RETAIN_EXP + - k) + 1) 3 c) (k + - 1) = CadState RETAIN_EXP 3 c.
{ rewrite <- Hp1_sum at 2.
  apply cad_run_silent_range PolicyPostStrip k ((RETAIN_EXP + - k) + 1) HL0_o 3 c (k + - 1) Hkm1_o.
  let j. assume Hj.
  claim Hjo : j :e omega. { exact nat_In_omega (k + - 1) Hkm1_o j Hj. }
  claim HL_o : ((RETAIN_EXP + - k) + 1) + j :e omega. { exact nat_add_omega ((RETAIN_EXP + - k) + 1) HL0_o j Hjo. }
  claim HL_lt80 : ((RETAIN_EXP + - k) + 1) + j < RETAIN_EXP.
  { rewrite <- Hp1_sum at 2.
    exact add_SNo_Lt2 ((RETAIN_EXP + - k) + 1) j (k + - 1) (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) (omega_SNo j Hjo) (omega_SNo (k + - 1) Hkm1_o)
          (nat_In_SNoLt (k + - 1) Hkm1_o j Hj). }
  claim HL_ge60 : 3 * INTERVAL_EXP <= ((RETAIN_EXP + - k) + 1) + j.
  { apply SNoLe_tra (3 * INTERVAL_EXP) (RETAIN_EXP + - k) (((RETAIN_EXP + - k) + 1) + j)
          (omega_SNo (3 * INTERVAL_EXP) n60_omega) (omega_SNo (RETAIN_EXP + - k) Hsub_o) (omega_SNo (((RETAIN_EXP + - k) + 1) + j) HL_o) Hsub_ge60.
    apply SNoLe_tra (RETAIN_EXP + - k) ((RETAIN_EXP + - k) + 1) (((RETAIN_EXP + - k) + 1) + j)
          (omega_SNo (RETAIN_EXP + - k) Hsub_o) (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) (omega_SNo (((RETAIN_EXP + - k) + 1) + j) HL_o).
    - rewrite <- add_SNo_0R (RETAIN_EXP + - k) (omega_SNo (RETAIN_EXP + - k) Hsub_o) at 1.
      exact add_SNo_Le2 (RETAIN_EXP + - k) 0 1 (omega_SNo (RETAIN_EXP + - k) Hsub_o) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
    - rewrite <- add_SNo_0R ((RETAIN_EXP + - k) + 1) (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) at 1.
      exact add_SNo_Le2 ((RETAIN_EXP + - k) + 1) 0 j (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) SNo_0 (omega_SNo j Hjo) (nat_0_Le j Hjo). }
  apply andI.
  - exact SNoLt_tra (((RETAIN_EXP + - k) + 1) + j) RETAIN_EXP MAX_EXP (omega_SNo (((RETAIN_EXP + - k) + 1) + j) HL_o) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo MAX_EXP n100_omega) HL_lt80 n80_lt_100.
  - rewrite bucket20_60_to_79 (((RETAIN_EXP + - k) + 1) + j) HL_o HL_ge60 HL_lt80.
    exact SNoLt_irref 3. }
rewrite Hphase1.
rewrite cad_run_1 PolicyPostStrip k (CadState RETAIN_EXP 3 c).
rewrite cad_step_at_80_from_3 PolicyPostStrip k c.
rewrite cad_run_add PolicyPostStrip k (CadState (RETAIN_EXP + 1) 4 (c + 1)) (10 + 9) n19_omega 1 nat_1_omega.
claim Hphase3 : cad_run PolicyPostStrip k (CadState (RETAIN_EXP + 1) 4 (c + 1)) (10 + 9) = CadState MAX_EXP 4 (c + 1).
{ rewrite <- Hp3_sum.
  apply cad_run_silent_range PolicyPostStrip k (RETAIN_EXP + 1) H81_o 4 (c + 1) (10 + 9) n19_omega.
  let j. assume Hj.
  claim Hjo : j :e omega. { exact nat_In_omega (10 + 9) n19_omega j Hj. }
  claim HL_o : (RETAIN_EXP + 1) + j :e omega. { exact nat_add_omega (RETAIN_EXP + 1) H81_o j Hjo. }
  claim HL_lt : (RETAIN_EXP + 1) + j < MAX_EXP.
  { rewrite <- Hp3_sum.
    exact add_SNo_Lt2 (RETAIN_EXP + 1) j (10 + 9) (omega_SNo (RETAIN_EXP + 1) H81_o) (omega_SNo j Hjo) (omega_SNo (10 + 9) n19_omega)
          (nat_In_SNoLt (10 + 9) n19_omega j Hj). }
  claim HL_ge80 : RETAIN_EXP <= (RETAIN_EXP + 1) + j.
  { apply SNoLe_tra RETAIN_EXP (RETAIN_EXP + 1) ((RETAIN_EXP + 1) + j) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo (RETAIN_EXP + 1) H81_o) (omega_SNo ((RETAIN_EXP + 1) + j) HL_o).
    - rewrite <- add_SNo_0R RETAIN_EXP (omega_SNo RETAIN_EXP n80_omega) at 1.
      exact add_SNo_Le2 RETAIN_EXP 0 1 (omega_SNo RETAIN_EXP n80_omega) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
    - rewrite <- add_SNo_0R (RETAIN_EXP + 1) (omega_SNo (RETAIN_EXP + 1) H81_o) at 1.
      exact add_SNo_Le2 (RETAIN_EXP + 1) 0 j (omega_SNo (RETAIN_EXP + 1) H81_o) SNo_0 (omega_SNo j Hjo) (nat_0_Le j Hjo). }
  apply andI.
  - exact HL_lt.
  - rewrite bucket20_80_to_99 ((RETAIN_EXP + 1) + j) HL_o HL_ge80 HL_lt.
    exact SNoLt_irref 4. }
rewrite Hphase3.
rewrite cad_run_1 PolicyPostStrip k (CadState MAX_EXP 4 (c + 1)).
rewrite cad_step_at_100 PolicyPostStrip k (c + 1).
rewrite If_i_0 (PolicyPostStrip = PolicyPreStrip) (bucket20 RETAIN_EXP) (bucket20 (RETAIN_EXP + - k)) PolicyPostStrip_neq_PreStrip.
rewrite bucket20_60_to_79 (RETAIN_EXP + - k) Hsub_o Hsub_ge60 Hsub_lt80.
rewrite n2_eq_1_plus_1.
rewrite add_SNo_assoc c 1 1 (omega_SNo c Hc) SNo_1 SNo_1.
reflexivity.
Qed.

(** COROLLARY (Cadence Dichotomy):
    Original pre-strip has identical cleanup counts per cycle (c + 1 = c + 1)
    for k = 0 and any 1 <= k <= 20; post-strip breaks this uniformity (c + 1 < c + 2,
    hence strictly unequal). *)
Theorem post_strip_cadence_asymmetry :
  forall k :e omega, 1 <= k -> k <= INTERVAL_EXP -> forall c :e omega,
  cad_count (cad_run PolicyPreStrip 0 (CadState (RETAIN_EXP + 1) 4 c) INTERVAL_EXP)
    = cad_count (cad_run PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) (INTERVAL_EXP + k)) /\
  cad_count (cad_run PolicyPostStrip 0 (CadState (RETAIN_EXP + 1) 4 c) INTERVAL_EXP)
    <> cad_count (cad_run PolicyPostStrip k (CadState ((RETAIN_EXP + - k) + 1) 3 c) (INTERVAL_EXP + k)).
let k. assume Hk H1k Hkle. let c. assume Hc.
claim Hpre0 : cad_run PolicyPreStrip 0 (CadState (RETAIN_EXP + 1) 4 c) INTERVAL_EXP = CadState (RETAIN_EXP + 1) 4 (c + 1).
{ claim H80 : RETAIN_EXP = RETAIN_EXP + - 0.
  { rewrite minus_SNo_0. symmetry. exact add_SNo_0R RETAIN_EXP (omega_SNo RETAIN_EXP n80_omega). }
  claim H20 : INTERVAL_EXP = INTERVAL_EXP + 0.
  { symmetry. exact add_SNo_0R INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega). }
  rewrite H80. rewrite H20.
  exact original_full_cycle_uniform_1 0 nat_0_omega (nat_0_Le INTERVAL_EXP n20_omega) c Hc. }
claim Hprek : cad_run PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) (INTERVAL_EXP + k) = CadState ((RETAIN_EXP + - k) + 1) 4 (c + 1).
{ exact original_full_cycle_uniform_1 k Hk Hkle c Hc. }
claim Hpost0 : cad_run PolicyPostStrip 0 (CadState (RETAIN_EXP + 1) 4 c) INTERVAL_EXP = CadState (RETAIN_EXP + 1) 4 (c + 1).
{ exact post_strip_full_cycle_k0_is_1 c Hc. }
claim Hpostk : cad_run PolicyPostStrip k (CadState ((RETAIN_EXP + - k) + 1) 3 c) (INTERVAL_EXP + k) = CadState ((RETAIN_EXP + - k) + 1) 3 (c + 2).
{ exact post_strip_full_cycle_kpos_is_2 k Hk H1k Hkle c Hc. }
apply andI.
- rewrite Hpre0. rewrite Hprek.
  rewrite cad_count_mk (RETAIN_EXP + 1) 4 (c + 1).
  rewrite cad_count_mk ((RETAIN_EXP + - k) + 1) 4 (c + 1).
  reflexivity.
- rewrite Hpost0. rewrite Hpostk.
  rewrite cad_count_mk (RETAIN_EXP + 1) 4 (c + 1).
  rewrite cad_count_mk ((RETAIN_EXP + - k) + 1) 3 (c + 2).
  assume Heq : c + 1 = c + 2.
  claim Hlt : c + 1 < c + 2.
  { rewrite n2_eq_1_plus_1.
    rewrite add_SNo_assoc c 1 1 (omega_SNo c Hc) SNo_1 SNo_1.
    rewrite <- add_SNo_0R (c + 1) (SNo_add_SNo c 1 (omega_SNo c Hc) SNo_1) at 1.
    exact add_SNo_Lt2 (c + 1) 0 1 (SNo_add_SNo c 1 (omega_SNo c Hc) SNo_1) SNo_0 SNo_1 SNoLt_0_1. }
  apply SNoLt_irref (c + 1).
  rewrite Heq at 2. exact Hlt.
Qed.

(** STARTUP DELAY THEOREM:
    Under BOTH bucketed policies (pre-strip and post-strip), loading an uncleaned
    history of length L0 in [80, 100) with k = 0 leading orphans initializes
    cleanup_bucket = 4, causing ZERO cleanups across all remaining turns until L = 100. *)
Theorem startup_uncleaned_k0_waits_to_100 :
  forall policy k, forall L0 :e omega, RETAIN_EXP <= L0 -> L0 < MAX_EXP ->
  cad_run policy k (CadState L0 (bucket20 L0) 0) (MAX_EXP + - L0) = CadState MAX_EXP 4 0.
let policy k. let L0. assume HL0 Hge80 Hlt100.
claim Hle100 : L0 <= MAX_EXP. { exact SNoLtLe L0 MAX_EXP Hlt100. }
claim Ht_o : MAX_EXP + - L0 :e omega. { exact nat_sub_omega L0 HL0 MAX_EXP n100_omega Hle100. }
claim Hsum : L0 + (MAX_EXP + - L0) = MAX_EXP. { exact SNo_add_sub_L MAX_EXP L0 (omega_SNo MAX_EXP n100_omega) (omega_SNo L0 HL0). }
rewrite bucket20_80_to_99 L0 HL0 Hge80 Hlt100.
rewrite <- Hsum at 2.
apply cad_run_silent_range policy k L0 HL0 4 0 (MAX_EXP + - L0) Ht_o.
let j. assume Hj.
claim Hjo : j :e omega. { exact nat_In_omega (MAX_EXP + - L0) Ht_o j Hj. }
claim HL_o : L0 + j :e omega. { exact nat_add_omega L0 HL0 j Hjo. }
claim HL_lt : L0 + j < MAX_EXP.
{ rewrite <- Hsum.
  exact add_SNo_Lt2 L0 j (MAX_EXP + - L0) (omega_SNo L0 HL0) (omega_SNo j Hjo) (omega_SNo (MAX_EXP + - L0) Ht_o)
        (nat_In_SNoLt (MAX_EXP + - L0) Ht_o j Hj). }
claim HL_ge80 : RETAIN_EXP <= L0 + j.
{ apply SNoLe_tra RETAIN_EXP L0 (L0 + j) (omega_SNo RETAIN_EXP n80_omega) (omega_SNo L0 HL0) (omega_SNo (L0 + j) HL_o) Hge80.
  rewrite <- add_SNo_0R L0 (omega_SNo L0 HL0) at 1.
  exact add_SNo_Le2 L0 0 j (omega_SNo L0 HL0) SNo_0 (omega_SNo j Hjo) (nat_0_Le j Hjo). }
apply andI.
- exact HL_lt.
- rewrite bucket20_80_to_99 (L0 + j) HL_o HL_ge80 HL_lt.
  exact SNoLt_irref 4.
Qed.

(** ---- Theorem Group 6: Pure Stateless Idempotent Normalizer & Startup Fix --
    Formalizes the two clean architectural alternatives to bucketed cleanup:
      A. Stateless pure normalizer:
           normalize_experience M R P s := cleanup_old_messages P (hygiene_step M R s)
         Runs structure FIRST (trim + drop leading tools), cosmetics SECOND (cleanup),
         needs ZERO bucket state, is EXACTLY IDEMPOTENT (normalize (normalize s) = normalize s),
         and enforces ValidSeq, len < M, ToolPaired, NoLeadingTool, AND CleanedUp P
         uniformly on every turn (startup, ramp-up 0..99, and steady state).
      B. Uniform startup cleanup pass (startup_init P s := cleanup_old_messages P (drop_leading_tools s))
         establishes NoLeadingTool /\ CleanedUp P at turn 0 for all k (including k = 0)
         while preserving the original uniform 1-cleanup/cycle steady-state cadence. *)

Theorem RoleRaw_neq_Tool : RoleRaw <> RoleTool.
assume Heq : 4 = 3.
apply SNoLt_irref 3.
rewrite <- Heq at 2.
exact nat_In_SNoLt 4 (nat_p_omega 4 nat_4) 3 In_3_4.
Qed.

Theorem RoleRaw_neq_Assistant : RoleRaw <> RoleAssistant.
assume Heq : 4 = 2.
apply SNoLt_irref 2.
rewrite <- Heq at 2.
exact nat_In_SNoLt 4 (nat_p_omega 4 nat_4) 2 In_2_4.
Qed.

Definition CleanOpsIdempotent : prop :=
  (forall x, trunc_tool (trunc_tool x) = trunc_tool x) /\
  (forall x, strip_reasoning (strip_reasoning x) = strip_reasoning x).

Definition CleanedUp : set -> set -> prop :=
  fun P s => forall i :e seq_len s, i + P < seq_len s -> clean_msg (seq_at s i) = seq_at s i.

Theorem clean_msg_idempotent : CleanOpsIdempotent -> forall m, clean_msg (clean_msg m) = clean_msg m.
assume Hidem. apply Hidem. assume Htr Hst.
let m.
apply xm (msg_role m = RoleTool).
- assume Ht : msg_role m = RoleTool.
  claim Hcm : clean_msg m = Msg RoleTool (trunc_tool (msg_content m)).
  { exact If_i_1 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
          (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
           else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Ht. }
  rewrite Hcm.
  claim Href : msg_role (Msg RoleTool (trunc_tool (msg_content m))) = RoleTool.
  { exact msg_role_pair RoleTool (trunc_tool (msg_content m)). }
  prove (if msg_role (Msg RoleTool (trunc_tool (msg_content m))) = RoleTool
         then Msg RoleTool (trunc_tool (msg_content (Msg RoleTool (trunc_tool (msg_content m)))))
         else if msg_role (Msg RoleTool (trunc_tool (msg_content m))) = RoleAssistant
         then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleTool (trunc_tool (msg_content m)))))
         else if msg_role (Msg RoleTool (trunc_tool (msg_content m))) = RoleRaw
         then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleTool (trunc_tool (msg_content m)))))
         else Msg RoleTool (trunc_tool (msg_content m)))
      = Msg RoleTool (trunc_tool (msg_content m)).
  rewrite If_i_1 (msg_role (Msg RoleTool (trunc_tool (msg_content m))) = RoleTool)
          (Msg RoleTool (trunc_tool (msg_content (Msg RoleTool (trunc_tool (msg_content m))))))
          (if msg_role (Msg RoleTool (trunc_tool (msg_content m))) = RoleAssistant
           then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleTool (trunc_tool (msg_content m)))))
           else if msg_role (Msg RoleTool (trunc_tool (msg_content m))) = RoleRaw
           then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleTool (trunc_tool (msg_content m)))))
           else Msg RoleTool (trunc_tool (msg_content m))) Href.
  rewrite msg_content_pair RoleTool (trunc_tool (msg_content m)).
  rewrite Htr (msg_content m).
  reflexivity.
- assume Hnt : msg_role m <> RoleTool.
  apply xm (msg_role m = RoleAssistant).
  + assume Ha : msg_role m = RoleAssistant.
    claim Hcm : clean_msg m = Msg RoleAssistant (strip_reasoning (msg_content m)).
    { prove (if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
             else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
             else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
             else m) = Msg RoleAssistant (strip_reasoning (msg_content m)).
      rewrite If_i_0 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
              (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
               else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hnt.
      exact If_i_1 (msg_role m = RoleAssistant) (Msg RoleAssistant (strip_reasoning (msg_content m)))
            (if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Ha. }
    rewrite Hcm.
    claim Hnt' : msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) <> RoleTool.
    { rewrite msg_role_pair RoleAssistant (strip_reasoning (msg_content m)). exact RoleAssistant_neq_Tool. }
    claim Ha' : msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleAssistant.
    { exact msg_role_pair RoleAssistant (strip_reasoning (msg_content m)). }
    prove (if msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleTool
           then Msg RoleTool (trunc_tool (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m)))))
           else if msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleAssistant
           then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m)))))
           else if msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleRaw
           then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m)))))
           else Msg RoleAssistant (strip_reasoning (msg_content m)))
        = Msg RoleAssistant (strip_reasoning (msg_content m)).
    rewrite If_i_0 (msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleTool)
            (Msg RoleTool (trunc_tool (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m))))))
            (if msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleAssistant
             then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m)))))
             else if msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleRaw
             then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m)))))
             else Msg RoleAssistant (strip_reasoning (msg_content m))) Hnt'.
    rewrite If_i_1 (msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleAssistant)
            (Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m))))))
            (if msg_role (Msg RoleAssistant (strip_reasoning (msg_content m))) = RoleRaw
             then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleAssistant (strip_reasoning (msg_content m)))))
             else Msg RoleAssistant (strip_reasoning (msg_content m))) Ha'.
    rewrite msg_content_pair RoleAssistant (strip_reasoning (msg_content m)).
    rewrite Hst (msg_content m).
    reflexivity.
  + assume Hna : msg_role m <> RoleAssistant.
    apply xm (msg_role m = RoleRaw).
    * assume Hr : msg_role m = RoleRaw.
      claim Hcm : clean_msg m = Msg RoleRaw (strip_reasoning (msg_content m)).
      { prove (if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
               else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
               else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
               else m) = Msg RoleRaw (strip_reasoning (msg_content m)).
        rewrite If_i_0 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
                (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
                 else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hnt.
        rewrite If_i_0 (msg_role m = RoleAssistant) (Msg RoleAssistant (strip_reasoning (msg_content m)))
                (if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hna.
        exact If_i_1 (msg_role m = RoleRaw) (Msg RoleRaw (strip_reasoning (msg_content m))) m Hr. }
      rewrite Hcm.
      claim Hnt' : msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) <> RoleTool.
      { rewrite msg_role_pair RoleRaw (strip_reasoning (msg_content m)). exact RoleRaw_neq_Tool. }
      claim Hna' : msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) <> RoleAssistant.
      { rewrite msg_role_pair RoleRaw (strip_reasoning (msg_content m)). exact RoleRaw_neq_Assistant. }
      claim Hr' : msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleRaw.
      { exact msg_role_pair RoleRaw (strip_reasoning (msg_content m)). }
      prove (if msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleTool
             then Msg RoleTool (trunc_tool (msg_content (Msg RoleRaw (strip_reasoning (msg_content m)))))
             else if msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleAssistant
             then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleRaw (strip_reasoning (msg_content m)))))
             else if msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleRaw
             then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleRaw (strip_reasoning (msg_content m)))))
             else Msg RoleRaw (strip_reasoning (msg_content m)))
          = Msg RoleRaw (strip_reasoning (msg_content m)).
      rewrite If_i_0 (msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleTool)
              (Msg RoleTool (trunc_tool (msg_content (Msg RoleRaw (strip_reasoning (msg_content m))))))
              (if msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleAssistant
               then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleRaw (strip_reasoning (msg_content m)))))
               else if msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleRaw
               then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleRaw (strip_reasoning (msg_content m)))))
               else Msg RoleRaw (strip_reasoning (msg_content m))) Hnt'.
      rewrite If_i_0 (msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleAssistant)
              (Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleRaw (strip_reasoning (msg_content m))))))
              (if msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleRaw
               then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleRaw (strip_reasoning (msg_content m)))))
               else Msg RoleRaw (strip_reasoning (msg_content m))) Hna'.
      rewrite If_i_1 (msg_role (Msg RoleRaw (strip_reasoning (msg_content m))) = RoleRaw)
              (Msg RoleRaw (strip_reasoning (msg_content (Msg RoleRaw (strip_reasoning (msg_content m))))))
              (Msg RoleRaw (strip_reasoning (msg_content m))) Hr'.
      rewrite msg_content_pair RoleRaw (strip_reasoning (msg_content m)).
      rewrite Hst (msg_content m).
      reflexivity.
    * assume Hnr : msg_role m <> RoleRaw.
      claim Hcm : clean_msg m = m.
      { prove (if msg_role m = RoleTool then Msg RoleTool (trunc_tool (msg_content m))
               else if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
               else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m))
               else m) = m.
        rewrite If_i_0 (msg_role m = RoleTool) (Msg RoleTool (trunc_tool (msg_content m)))
                (if msg_role m = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content m))
                 else if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hnt.
        rewrite If_i_0 (msg_role m = RoleAssistant) (Msg RoleAssistant (strip_reasoning (msg_content m)))
                (if msg_role m = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content m)) else m) Hna.
        exact If_i_0 (msg_role m = RoleRaw) (Msg RoleRaw (strip_reasoning (msg_content m))) m Hnr. }
      rewrite Hcm. exact Hcm.
Qed.

Theorem cleanup_establishes_CleanedUp : CleanOpsIdempotent -> forall P s,
  CleanedUp P (cleanup_old_messages P s).
assume Hidem. let P s.
let i. assume Hi Hlt.
claim Hi' : i :e seq_len s. { rewrite <- cleanup_preserves_len P s. exact Hi. }
claim Hlt' : i + P < seq_len s. { rewrite <- cleanup_preserves_len P s. exact Hlt. }
claim Hat : seq_at (cleanup_old_messages P s) i = clean_msg (seq_at s i).
{ prove seq_at (Seq (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j)) i = clean_msg (seq_at s i).
  rewrite seq_at_mk (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j) i Hi'.
  exact If_i_1 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hlt'. }
rewrite Hat.
exact clean_msg_idempotent Hidem (seq_at s i).
Qed.

Theorem cleanup_idempotent : CleanOpsIdempotent -> forall P s,
  cleanup_old_messages P (cleanup_old_messages P s) = cleanup_old_messages P s.
assume Hidem. let P s.
prove setsum (seq_len (cleanup_old_messages P s))
             (fun i :e seq_len (cleanup_old_messages P s) =>
               if i + P < seq_len (cleanup_old_messages P s)
               then clean_msg (seq_at (cleanup_old_messages P s) i)
               else seq_at (cleanup_old_messages P s) i)
    = setsum (seq_len s)
             (fun i :e seq_len s =>
               if i + P < seq_len s then clean_msg (seq_at s i) else seq_at s i).
rewrite cleanup_preserves_len P s.
claim Hlam : (fun i :e seq_len s =>
                if i + P < seq_len s
                then clean_msg (seq_at (cleanup_old_messages P s) i)
                else seq_at (cleanup_old_messages P s) i)
           = (fun i :e seq_len s =>
                if i + P < seq_len s then clean_msg (seq_at s i) else seq_at s i).
{ apply lam_ext (seq_len s).
  let i. assume Hi.
  prove (if i + P < seq_len s then clean_msg (seq_at (cleanup_old_messages P s) i) else seq_at (cleanup_old_messages P s) i)
      = (if i + P < seq_len s then clean_msg (seq_at s i) else seq_at s i).
  claim Hat : seq_at (cleanup_old_messages P s) i = (if i + P < seq_len s then clean_msg (seq_at s i) else seq_at s i).
  { exact seq_at_mk (seq_len s) (fun j => if j + P < seq_len s then clean_msg (seq_at s j) else seq_at s j) i Hi. }
  apply xm (i + P < seq_len s).
  - assume Hlt : i + P < seq_len s.
    rewrite If_i_1 (i + P < seq_len s) (clean_msg (seq_at (cleanup_old_messages P s) i)) (seq_at (cleanup_old_messages P s) i) Hlt.
    rewrite If_i_1 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hlt.
    rewrite Hat.
    rewrite If_i_1 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hlt.
    exact clean_msg_idempotent Hidem (seq_at s i).
  - assume Hnlt : ~(i + P < seq_len s).
    rewrite If_i_0 (i + P < seq_len s) (clean_msg (seq_at (cleanup_old_messages P s) i)) (seq_at (cleanup_old_messages P s) i) Hnlt.
    rewrite If_i_0 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hnlt.
    rewrite Hat.
    exact If_i_0 (i + P < seq_len s) (clean_msg (seq_at s i)) (seq_at s i) Hnlt. }
rewrite Hlam. reflexivity.
Qed.

Theorem cleanup_preserves_NoLeadingTool : forall P s, ValidSeq s -> NoLeadingTool s ->
  NoLeadingTool (cleanup_old_messages P s).
let P s. assume Hs Hnlt.
prove seq_len (cleanup_old_messages P s) = 0 \/ msg_role (seq_at (cleanup_old_messages P s) 0) <> RoleTool.
apply Hnlt.
- assume H0 : seq_len s = 0.
  apply orIL. rewrite cleanup_preserves_len P s. exact H0.
- assume Hne : msg_role (seq_at s 0) <> RoleTool.
  apply xm (seq_len s = 0).
  + assume H0 : seq_len s = 0.
    apply orIL. rewrite cleanup_preserves_len P s. exact H0.
  + assume Hne0 : seq_len s <> 0.
    apply orIR.
    claim H0in : 0 :e seq_len s.
    { apply nat_SNoLe_cases 0 nat_0_omega (seq_len s) Hs (nat_0_Le (seq_len s) Hs).
      - assume H : 0 :e seq_len s. exact H.
      - assume H0 : 0 = seq_len s. apply FalseE. apply Hne0. symmetry. exact H0. }
    rewrite cleanup_preserves_roles P s 0 H0in.
    exact Hne.
Qed.

Theorem drop_leading_tools_cleanup_eq : forall P u, ValidSeq u -> NoLeadingTool u ->
  drop_leading_tools (cleanup_old_messages P u) = cleanup_old_messages P u.
let P u. assume Hu Hnlt.
claim Hv : ValidSeq (cleanup_old_messages P u).
{ prove seq_len (cleanup_old_messages P u) :e omega. rewrite cleanup_preserves_len P u. exact Hu. }
claim Hnlt_v : NoLeadingTool (cleanup_old_messages P u). { exact cleanup_preserves_NoLeadingTool P u Hu Hnlt. }
claim Hcut0 : lead_tool_cut (cleanup_old_messages P u) = 0.
{ apply lead_tool_cut_eq (cleanup_old_messages P u) Hv 0
        (nat_Le_In_ordsucc 0 nat_0_omega (seq_len (cleanup_old_messages P u)) Hv (nat_0_Le (seq_len (cleanup_old_messages P u)) Hv)).
  - let j. assume Hj. apply FalseE. exact EmptyE j Hj.
  - apply Hnlt_v.
    + assume H0 : seq_len (cleanup_old_messages P u) = 0. apply orIL. symmetry. exact H0.
    + assume Hne : msg_role (seq_at (cleanup_old_messages P u) 0) <> RoleTool. apply orIR. exact Hne. }
claim Hlen0 : seq_len (cleanup_old_messages P u) + - 0 = seq_len u.
{ rewrite cleanup_preserves_len P u. rewrite minus_SNo_0. exact add_SNo_0R (seq_len u) (omega_SNo (seq_len u) Hu). }
prove setsum (seq_len (cleanup_old_messages P u) + - lead_tool_cut (cleanup_old_messages P u))
             (fun i :e seq_len (cleanup_old_messages P u) + - lead_tool_cut (cleanup_old_messages P u) =>
               seq_at (cleanup_old_messages P u) (lead_tool_cut (cleanup_old_messages P u) + i))
    = setsum (seq_len u)
             (fun i :e seq_len u => if i + P < seq_len u then clean_msg (seq_at u i) else seq_at u i).
rewrite Hcut0. rewrite Hlen0.
claim Hlam : (fun i :e seq_len u => seq_at (cleanup_old_messages P u) (0 + i))
           = (fun i :e seq_len u => if i + P < seq_len u then clean_msg (seq_at u i) else seq_at u i).
{ apply lam_ext (seq_len u).
  let i. assume Hi.
  claim Hio : i :e omega. { exact nat_In_omega (seq_len u) Hu i Hi. }
  prove seq_at (cleanup_old_messages P u) (0 + i) = (if i + P < seq_len u then clean_msg (seq_at u i) else seq_at u i).
  rewrite add_SNo_0L i (omega_SNo i Hio).
  exact seq_at_mk (seq_len u) (fun j => if j + P < seq_len u then clean_msg (seq_at u j) else seq_at u j) i Hi. }
rewrite Hlam. reflexivity.
Qed.

Theorem hygiene_step_valid_lt_nlt : forall M :e omega, forall R :e omega, R < M ->
  forall s, ValidSeq s ->
  ValidSeq (hygiene_step M R s) /\ seq_len (hygiene_step M R s) < M /\ NoLeadingTool (hygiene_step M R s).
let M. assume HM. let R. assume HR HRM. let s. assume Hs.
apply xm (M <= seq_len s).
- assume Hge : M <= seq_len s.
  claim Htrim : window_trim M R s = seq_drop (seq_len s + - R) s.
  { exact If_i_1 (M <= seq_len s) (seq_drop (seq_len s + - R) s) s Hge. }
  claim Hw_len : seq_len (seq_drop (seq_len s + - R) s) = R.
  { prove seq_len (Seq (seq_len s + - (seq_len s + - R)) (fun i => seq_at s ((seq_len s + - R) + i))) = R.
    rewrite seq_len_mk (seq_len s + - (seq_len s + - R)) (fun i => seq_at s ((seq_len s + - R) + i)).
    rewrite minus_add_SNo_distr (seq_len s) (- R) (omega_SNo (seq_len s) Hs) (SNo_minus_SNo R (omega_SNo R HR)).
    rewrite minus_SNo_invol R (omega_SNo R HR).
    exact add_SNo_minus_L2' (seq_len s) R (omega_SNo (seq_len s) Hs) (omega_SNo R HR). }
  claim Hw_v : ValidSeq (seq_drop (seq_len s + - R) s).
  { prove seq_len (seq_drop (seq_len s + - R) s) :e omega. rewrite Hw_len. exact HR. }
  prove ValidSeq (drop_leading_tools (window_trim M R s)) /\
        seq_len (drop_leading_tools (window_trim M R s)) < M /\
        NoLeadingTool (drop_leading_tools (window_trim M R s)).
  rewrite Htrim.
  apply and3I.
  + exact drop_leading_tools_valid (seq_drop (seq_len s + - R) s) Hw_v.
  + apply SNoLeLt_tra (seq_len (drop_leading_tools (seq_drop (seq_len s + - R) s))) R M
          (omega_SNo (seq_len (drop_leading_tools (seq_drop (seq_len s + - R) s))) (drop_leading_tools_valid (seq_drop (seq_len s + - R) s) Hw_v))
          (omega_SNo R HR) (omega_SNo M HM).
    * rewrite <- Hw_len at 2. exact drop_leading_tools_len_le (seq_drop (seq_len s + - R) s) Hw_v.
    * exact HRM.
  + exact drop_leading_tools_NoLeadingTool (seq_drop (seq_len s + - R) s) Hw_v.
- assume Hnge : ~(M <= seq_len s).
  claim HltM : seq_len s < M.
  { apply SNoLtLe_or (seq_len s) M (omega_SNo (seq_len s) Hs) (omega_SNo M HM).
    - assume H : seq_len s < M. exact H.
    - assume H : M <= seq_len s. apply FalseE. exact Hnge H. }
  claim Htrim : window_trim M R s = s.
  { exact If_i_0 (M <= seq_len s) (seq_drop (seq_len s + - R) s) s Hnge. }
  prove ValidSeq (drop_leading_tools (window_trim M R s)) /\
        seq_len (drop_leading_tools (window_trim M R s)) < M /\
        NoLeadingTool (drop_leading_tools (window_trim M R s)).
  rewrite Htrim.
  apply and3I.
  + exact drop_leading_tools_valid s Hs.
  + exact SNoLeLt_tra (seq_len (drop_leading_tools s)) (seq_len s) M
          (omega_SNo (seq_len (drop_leading_tools s)) (drop_leading_tools_valid s Hs))
          (omega_SNo (seq_len s) Hs) (omega_SNo M HM) (drop_leading_tools_len_le s Hs) HltM.
  + exact drop_leading_tools_NoLeadingTool s Hs.
Qed.

(** Pure stateless experience normalizer: structure first (trim + drop leading tools),
    cosmetics second (cleanup old messages). Zero bucket state. *)
Definition normalize_experience : set -> set -> set -> set -> set :=
  fun M R P s => cleanup_old_messages P (hygiene_step M R s).

Theorem normalize_experience_idempotent : CleanOpsIdempotent ->
  forall M :e omega, forall R :e omega, R < M -> forall P s, ValidSeq s ->
  normalize_experience M R P (normalize_experience M R P s) = normalize_experience M R P s.
assume Hidem. let M. assume HM. let R. assume HR HRM. let P s. assume Hs.
claim Hh : ValidSeq (hygiene_step M R s) /\ seq_len (hygiene_step M R s) < M /\ NoLeadingTool (hygiene_step M R s).
{ exact hygiene_step_valid_lt_nlt M HM R HR HRM s Hs. }
apply Hh. assume Hh12 Hnlt. apply Hh12. assume Hhv Hhlt.
claim Hnge : ~(M <= seq_len (normalize_experience M R P s)).
{ assume Hle : M <= seq_len (cleanup_old_messages P (hygiene_step M R s)).
  claim Hle' : M <= seq_len (hygiene_step M R s).
  { rewrite <- cleanup_preserves_len P (hygiene_step M R s). exact Hle. }
  exact SNoLt_irref M (SNoLeLt_tra M (seq_len (hygiene_step M R s)) M (omega_SNo M HM) (omega_SNo (seq_len (hygiene_step M R s)) Hhv) (omega_SNo M HM) Hle' Hhlt). }
claim Htrim : window_trim M R (normalize_experience M R P s) = normalize_experience M R P s.
{ exact If_i_0 (M <= seq_len (normalize_experience M R P s))
        (seq_drop (seq_len (normalize_experience M R P s) + - R) (normalize_experience M R P s))
        (normalize_experience M R P s) Hnge. }
prove cleanup_old_messages P (drop_leading_tools (window_trim M R (normalize_experience M R P s))) = normalize_experience M R P s.
rewrite Htrim.
prove cleanup_old_messages P (drop_leading_tools (cleanup_old_messages P (hygiene_step M R s))) = cleanup_old_messages P (hygiene_step M R s).
rewrite drop_leading_tools_cleanup_eq P (hygiene_step M R s) Hhv Hnlt.
exact cleanup_idempotent Hidem P (hygiene_step M R s).
Qed.

Theorem normalize_experience_invariants : CleanOpsIdempotent ->
  forall M :e omega, forall R :e omega, R < M -> forall P s, ValidSeq s -> ToolPaired s ->
  ValidSeq (normalize_experience M R P s) /\
  seq_len (normalize_experience M R P s) < M /\
  ToolPaired (normalize_experience M R P s) /\
  NoLeadingTool (normalize_experience M R P s) /\
  CleanedUp P (normalize_experience M R P s).
assume Hidem. let M. assume HM. let R. assume HR HRM. let P s. assume Hs Htp.
claim Hh : ValidSeq (hygiene_step M R s) /\ seq_len (hygiene_step M R s) < M /\ ToolPaired (hygiene_step M R s).
{ exact hygiene_step_bounded_and_paired M HM R HR HRM s Hs Htp. }
apply Hh. assume Hh12 Hhtp. apply Hh12. assume Hhv Hhlt.
claim Hnv : ValidSeq (normalize_experience M R P s).
{ prove seq_len (cleanup_old_messages P (hygiene_step M R s)) :e omega.
  rewrite cleanup_preserves_len P (hygiene_step M R s). exact Hhv. }
claim Hnlt_len : seq_len (normalize_experience M R P s) < M.
{ prove seq_len (cleanup_old_messages P (hygiene_step M R s)) < M.
  rewrite cleanup_preserves_len P (hygiene_step M R s). exact Hhlt. }
claim Hntp : ToolPaired (normalize_experience M R P s).
{ exact cleanup_preserves_ToolPaired P (hygiene_step M R s) Hhv Hhtp. }
apply andI.
- apply andI.
  + apply andI.
    * apply andI.
      { exact Hnv. }
      { exact Hnlt_len. }
    * exact Hntp.
  + exact ToolPaired_implies_NoLeadingTool (normalize_experience M R P s) Hnv Hntp.
- exact cleanup_establishes_CleanedUp Hidem P (hygiene_step M R s).
Qed.

(** Alternative B: Uniform startup cleanup pass (establishes NoLeadingTool and CleanedUp
    immediately at turn 0 for ALL k, including k = 0, while keeping the original
    PolicyPreStrip loop uniformly at 1 cleanup per cycle). *)
Definition startup_init : set -> set -> set :=
  fun P s => cleanup_old_messages P (drop_leading_tools s).

Theorem startup_init_establishes_clean_no_leading_tool : CleanOpsIdempotent ->
  forall P s, ValidSeq s ->
  ValidSeq (startup_init P s) /\ NoLeadingTool (startup_init P s) /\ CleanedUp P (startup_init P s).
assume Hidem. let P s. assume Hs.
claim Hd_v : ValidSeq (drop_leading_tools s). { exact drop_leading_tools_valid s Hs. }
claim Hd_nlt : NoLeadingTool (drop_leading_tools s). { exact drop_leading_tools_NoLeadingTool s Hs. }
apply and3I.
- prove seq_len (cleanup_old_messages P (drop_leading_tools s)) :e omega.
  rewrite cleanup_preserves_len P (drop_leading_tools s). exact Hd_v.
- exact cleanup_preserves_NoLeadingTool P (drop_leading_tools s) Hd_v Hd_nlt.
- exact cleanup_establishes_CleanedUp Hidem P (drop_leading_tools s).
Qed.

(** ---- Theorem Group 7: General k <= 80 Uniformity & Prompt-Cache Prefix Stability
    1. Proves IsBucket20_exists on all of omega, generalizing original pre-strip
       uniformity (1 cleanup per (20 + k)-step cycle, with (19 + k) silent turns)
       to EVERY 0 <= k <= RETAIN_EXP (0..80), not only 0..20.
    2. Defines PrefixOf s1 s2 (strict LLM KV-cache prefix preservation) and
       seq_snoc s m (appending one message).
    3. Proves that every silent non-jump turn under the 20-message jump cadence
       preserves PrefixOf identically, whereas per-turn normalize_experience
       provably breaks PrefixOf at index (len - P) whenever an uncleaned tool or
       reasoning message ages out of the P-message preserve tail (with a concrete
       witness at len = 80, P = 10 that is already ToolPaired and CleanedUp 10). *)

Theorem IsBucket20_exists : forall L :e omega, exists b, IsBucket20 L b.
let L. assume HL.
apply nat_ind (fun m => exists b, IsBucket20 m b).
- prove exists b, IsBucket20 0 b.
  witness 0.
  prove 0 :e omega /\ 0 * INTERVAL_EXP <= 0 /\ 0 < (0 + 1) * INTERVAL_EXP.
  rewrite mul_SNo_zeroL INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega).
  rewrite add_SNo_0L 1 SNo_1.
  rewrite mul_SNo_oneL INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega).
  apply and3I.
  + exact nat_0_omega.
  + exact SNoLe_ref 0.
  + exact n20_pos.
- let m. assume Hm IH.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  apply IH. let b. assume Hb.
  apply Hb. assume Hb1 Hmlt. apply Hb1. assume Hbo Hble.
  claim Hb1o : b + 1 :e omega. { exact nat_add_omega b Hbo 1 nat_1_omega. }
  claim Hbm1o : (b + 1) * INTERVAL_EXP :e omega. { exact nat_mul_omega (b + 1) Hb1o INTERVAL_EXP n20_omega. }
  claim Hm1o : m + 1 :e omega. { exact nat_add_omega m Hmo 1 nat_1_omega. }
  claim Hle_succ : m + 1 <= (b + 1) * INTERVAL_EXP.
  { exact nat_SNoLt_S_Le m Hmo ((b + 1) * INTERVAL_EXP) Hbm1o Hmlt. }
  prove exists b', IsBucket20 (ordsucc m) b'.
  rewrite ordsucc_eq_add_1 m Hmo.
  apply nat_SNoLe_cases (m + 1) Hm1o ((b + 1) * INTERVAL_EXP) Hbm1o Hle_succ.
  + assume Hin : m + 1 :e (b + 1) * INTERVAL_EXP.
    witness b.
    prove b :e omega /\ b * INTERVAL_EXP <= m + 1 /\ m + 1 < (b + 1) * INTERVAL_EXP.
    apply and3I.
    * exact Hbo.
    * apply SNoLe_tra (b * INTERVAL_EXP) m (m + 1)
            (omega_SNo (b * INTERVAL_EXP) (nat_mul_omega b Hbo INTERVAL_EXP n20_omega))
            (omega_SNo m Hmo) (omega_SNo (m + 1) Hm1o) Hble.
      rewrite <- add_SNo_0R m (omega_SNo m Hmo) at 1.
      exact add_SNo_Le2 m 0 1 (omega_SNo m Hmo) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
    * exact nat_In_SNoLt ((b + 1) * INTERVAL_EXP) Hbm1o (m + 1) Hin.
  + assume Heq : m + 1 = (b + 1) * INTERVAL_EXP.
    witness (b + 1).
    prove b + 1 :e omega /\ (b + 1) * INTERVAL_EXP <= m + 1 /\ m + 1 < ((b + 1) + 1) * INTERVAL_EXP.
    apply and3I.
    * exact Hb1o.
    * rewrite Heq. exact SNoLe_ref ((b + 1) * INTERVAL_EXP).
    * rewrite Heq.
      rewrite mul_SNo_distrR (b + 1) 1 INTERVAL_EXP (omega_SNo (b + 1) Hb1o) SNo_1 (omega_SNo INTERVAL_EXP n20_omega).
      rewrite mul_SNo_oneL INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega).
      rewrite <- add_SNo_0R ((b + 1) * INTERVAL_EXP) (omega_SNo ((b + 1) * INTERVAL_EXP) Hbm1o) at 1.
      exact add_SNo_Lt2 ((b + 1) * INTERVAL_EXP) 0 INTERVAL_EXP
            (omega_SNo ((b + 1) * INTERVAL_EXP) Hbm1o) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) n20_pos.
- exact omega_nat_p L HL.
Qed.

Theorem bucket20_spec : forall L :e omega, IsBucket20 L (bucket20 L).
let L. assume HL.
exact Eps_i_ex (fun b => IsBucket20 L b) (IsBucket20_exists L HL).
Qed.

Theorem bucket20_not_gt_4_below_100 : forall L :e omega, L < MAX_EXP -> ~(4 < bucket20 L).
let L. assume HL Hlt100 H4b.
claim Hspec : IsBucket20 L (bucket20 L). { exact bucket20_spec L HL. }
apply Hspec. assume Hb1 _. apply Hb1. assume Hbo Hble.
claim H5le : 5 <= bucket20 L.
{ rewrite n5_eq_4_plus_1. exact nat_SNoLt_S_Le 4 (nat_p_omega 4 nat_4) (bucket20 L) Hbo H4b. }
claim H100le : MAX_EXP <= bucket20 L * INTERVAL_EXP.
{ exact nat_mul_20_mono 5 (nat_p_omega 5 nat_5) (bucket20 L) Hbo H5le. }
claim H100leL : MAX_EXP <= L.
{ exact SNoLe_tra MAX_EXP (bucket20 L * INTERVAL_EXP) L
        (omega_SNo MAX_EXP n100_omega)
        (omega_SNo (bucket20 L * INTERVAL_EXP) (nat_mul_omega (bucket20 L) Hbo INTERVAL_EXP n20_omega))
        (omega_SNo L HL) H100le Hble. }
exact SNoLt_irref L (SNoLtLe_tra L MAX_EXP L (omega_SNo L HL) (omega_SNo MAX_EXP n100_omega) (omega_SNo L HL) Hlt100 H100leL).
Qed.

(** Generalized silent-stretch and full-cycle uniformity for ALL 0 <= k <= 80. *)
Theorem original_silent_stretch_all_k :
  forall k :e omega, k <= RETAIN_EXP -> forall c :e omega,
  cad_run PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) ((10 + 9) + k) =
  CadState MAX_EXP 4 c.
let k. assume Hk Hk80. let c. assume Hc.
claim Hsub_o : RETAIN_EXP + - k :e omega. { exact nat_sub_omega k Hk RETAIN_EXP n80_omega Hk80. }
claim HL0_o : (RETAIN_EXP + - k) + 1 :e omega. { exact nat_add_omega (RETAIN_EXP + - k) Hsub_o 1 nat_1_omega. }
claim Hts_o : (10 + 9) + k :e omega. { exact nat_add_omega (10 + 9) n19_omega k Hk. }
claim Hsum : ((RETAIN_EXP + - k) + 1) + ((10 + 9) + k) = MAX_EXP.
{ claim HS80k : SNo (RETAIN_EXP + - k). { exact omega_SNo (RETAIN_EXP + - k) Hsub_o. }
  claim HS19 : SNo (10 + 9). { exact omega_SNo (10 + 9) n19_omega. }
  claim HSk : SNo k. { exact omega_SNo k Hk. }
  rewrite add_SNo_com (10 + 9) k HS19 HSk.
  rewrite add_SNo_assoc ((RETAIN_EXP + - k) + 1) k (10 + 9) (SNo_add_SNo (RETAIN_EXP + - k) 1 HS80k SNo_1) HSk HS19.
  rewrite <- add_SNo_assoc (RETAIN_EXP + - k) 1 k HS80k SNo_1 HSk.
  rewrite add_SNo_com 1 k SNo_1 HSk.
  rewrite add_SNo_assoc (RETAIN_EXP + - k) k 1 HS80k HSk SNo_1.
  rewrite add_SNo_com (RETAIN_EXP + - k) k HS80k HSk.
  rewrite SNo_add_sub_L RETAIN_EXP k (omega_SNo RETAIN_EXP n80_omega) HSk.
  rewrite <- add_SNo_assoc RETAIN_EXP 1 (10 + 9) (omega_SNo RETAIN_EXP n80_omega) SNo_1 HS19.
  rewrite add_SNo_com 1 (10 + 9) SNo_1 HS19.
  rewrite <- n20_eq_19_plus_1.
  symmetry. exact n100_eq_80_plus_20. }
rewrite <- Hsum.
apply cad_run_silent_range PolicyPreStrip k ((RETAIN_EXP + - k) + 1) HL0_o 4 c ((10 + 9) + k) Hts_o.
let j. assume Hj.
claim Hjo : j :e omega. { exact nat_In_omega ((10 + 9) + k) Hts_o j Hj. }
claim HL_o : ((RETAIN_EXP + - k) + 1) + j :e omega. { exact nat_add_omega ((RETAIN_EXP + - k) + 1) HL0_o j Hjo. }
claim HL_lt : ((RETAIN_EXP + - k) + 1) + j < MAX_EXP.
{ rewrite <- Hsum.
  exact add_SNo_Lt2 ((RETAIN_EXP + - k) + 1) j ((10 + 9) + k)
        (omega_SNo ((RETAIN_EXP + - k) + 1) HL0_o) (omega_SNo j Hjo) (omega_SNo ((10 + 9) + k) Hts_o)
        (nat_In_SNoLt ((10 + 9) + k) Hts_o j Hj). }
apply andI.
- exact HL_lt.
- exact bucket20_not_gt_4_below_100 (((RETAIN_EXP + - k) + 1) + j) HL_o HL_lt.
Qed.

Theorem original_full_cycle_uniform_all_k :
  forall k :e omega, k <= RETAIN_EXP -> forall c :e omega,
  cad_run PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) (INTERVAL_EXP + k) =
  CadState ((RETAIN_EXP + - k) + 1) 4 (c + 1).
let k. assume Hk Hk80. let c. assume Hc.
claim Hts_o : (10 + 9) + k :e omega. { exact nat_add_omega (10 + 9) n19_omega k Hk. }
claim Htot_eq : INTERVAL_EXP + k = ((10 + 9) + k) + 1.
{ rewrite n20_eq_19_plus_1.
  rewrite <- add_SNo_assoc (10 + 9) 1 k (omega_SNo (10 + 9) n19_omega) SNo_1 (omega_SNo k Hk).
  rewrite add_SNo_com 1 k SNo_1 (omega_SNo k Hk).
  exact add_SNo_assoc (10 + 9) k 1 (omega_SNo (10 + 9) n19_omega) (omega_SNo k Hk) SNo_1. }
rewrite Htot_eq.
rewrite cad_run_add PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 c) ((10 + 9) + k) Hts_o 1 nat_1_omega.
rewrite original_silent_stretch_all_k k Hk Hk80 c Hc.
rewrite cad_run_1 PolicyPreStrip k (CadState MAX_EXP 4 c).
rewrite cad_step_at_100 PolicyPreStrip k c.
claim Href : PolicyPreStrip = PolicyPreStrip. { reflexivity. }
rewrite If_i_1 (PolicyPreStrip = PolicyPreStrip) (bucket20 RETAIN_EXP) (bucket20 (RETAIN_EXP + - k)) Href.
rewrite bucket20_80_to_99 RETAIN_EXP n80_omega (SNoLe_ref RETAIN_EXP) n80_lt_100.
reflexivity.
Qed.

(** Strict prefix relation: models LLM KV-cache prefix preservation across turns. *)
Definition PrefixOf : set -> set -> prop :=
  fun s1 s2 => seq_len s1 <= seq_len s2 /\ (forall i :e seq_len s1, seq_at s2 i = seq_at s1 i).

Definition seq_snoc : set -> set -> set :=
  fun s m => Seq (seq_len s + 1) (fun i => if i = seq_len s then m else seq_at s i).

Theorem seq_snoc_valid : forall s, ValidSeq s -> forall m, ValidSeq (seq_snoc s m).
let s. assume Hs. let m.
exact ValidSeq_mk (seq_len s + 1) (nat_add_omega (seq_len s) Hs 1 nat_1_omega) (fun i => if i = seq_len s then m else seq_at s i).
Qed.

Theorem seq_snoc_len : forall s m, seq_len (seq_snoc s m) = seq_len s + 1.
let s m. exact seq_len_mk (seq_len s + 1) (fun i => if i = seq_len s then m else seq_at s i).
Qed.

Theorem seq_snoc_PrefixOf : forall s, ValidSeq s -> forall m, PrefixOf s (seq_snoc s m).
let s. assume Hs. let m.
prove seq_len s <= seq_len (seq_snoc s m) /\ (forall i :e seq_len s, seq_at (seq_snoc s m) i = seq_at s i).
apply andI.
- rewrite seq_snoc_len s m.
  rewrite <- add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hs) at 1.
  exact add_SNo_Le2 (seq_len s) 0 1 (omega_SNo (seq_len s) Hs) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
- let i. assume Hi.
  claim Hio : i :e omega. { exact nat_In_omega (seq_len s) Hs i Hi. }
  claim Hilt : i < seq_len s. { exact nat_In_SNoLt (seq_len s) Hs i Hi. }
  claim Hne : i <> seq_len s.
  { assume Heq : i = seq_len s. apply SNoLt_irref i. rewrite Heq at 2. exact Hilt. }
  claim Hin1 : i :e seq_len s + 1.
  { rewrite <- ordsucc_eq_add_1 (seq_len s) Hs. exact ordsuccI1 (seq_len s) i Hi. }
  prove seq_at (Seq (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j)) i = seq_at s i.
  rewrite seq_at_mk (seq_len s + 1) (fun j => if j = seq_len s then m else seq_at s j) i Hin1.
  exact If_i_0 (i = seq_len s) m (seq_at s i) Hne.
Qed.

Theorem seq_snoc_preserves_NoLeadingTool : forall s, ValidSeq s -> 0 < seq_len s -> NoLeadingTool s ->
  forall m, NoLeadingTool (seq_snoc s m).
let s. assume Hs Hpos Hnlt. let m.
prove seq_len (seq_snoc s m) = 0 \/ msg_role (seq_at (seq_snoc s m) 0) <> RoleTool.
apply orIR.
claim H0in : 0 :e seq_len s. { exact nat_SNoLt_In (seq_len s) Hs 0 nat_0_omega Hpos. }
claim Hpref : PrefixOf s (seq_snoc s m). { exact seq_snoc_PrefixOf s Hs m. }
apply Hpref. assume _ Hat.
rewrite Hat 0 H0in.
apply Hnlt.
- assume H0 : seq_len s = 0.
  apply FalseE. apply SNoLt_irref 0. rewrite <- H0 at 2. exact Hpos.
- assume Hne : msg_role (seq_at s 0) <> RoleTool. exact Hne.
Qed.

(** PER-TURN NORMALIZATION CACHE-BUSTING THEOREM:
    Whenever a history s (with 0 < P <= len s and len s + 1 < M) has an uncleaned
    message right at the preserve boundary (index len s - P), appending one new
    message m and immediately applying per-turn normalize_experience rewrites
    index (len s - P), strictly breaking PrefixOf s (normalize (seq_snoc s m))
    and invalidating the KV-cache prefix for all P newest messages. *)
Theorem per_turn_normalize_breaks_prefix :
  forall M :e omega, forall R :e omega, R < M ->
  forall P :e omega, 0 < P ->
  forall s, ValidSeq s -> P <= seq_len s -> seq_len s + 1 < M -> NoLeadingTool s ->
  clean_msg (seq_at s (seq_len s + - P)) <> seq_at s (seq_len s + - P) ->
  forall m, ~(PrefixOf s (normalize_experience M R P (seq_snoc s m))).
let M. assume HM. let R. assume HR HRM. let P. assume HP HPpos.
let s. assume Hs HPs HltM Hnlt Hdirty. let m.
assume Hpref : PrefixOf s (normalize_experience M R P (seq_snoc s m)).
claim Hspos : 0 < seq_len s.
{ exact SNoLtLe_tra 0 P (seq_len s) SNo_0 (omega_SNo P HP) (omega_SNo (seq_len s) Hs) HPpos HPs. }
claim Hidx_o : seq_len s + - P :e omega. { exact nat_sub_omega P HP (seq_len s) Hs HPs. }
claim Hidx_lt : seq_len s + - P < seq_len s.
{ rewrite <- SNo_add_sub_L (seq_len s) P (omega_SNo (seq_len s) Hs) (omega_SNo P HP) at 2.
  rewrite <- add_SNo_0L (seq_len s + - P) (omega_SNo (seq_len s + - P) Hidx_o) at 1.
  exact add_SNo_Lt1 0 (seq_len s + - P) P SNo_0 (omega_SNo (seq_len s + - P) Hidx_o) (omega_SNo P HP) HPpos. }
claim Hidx_in : seq_len s + - P :e seq_len s. { exact nat_SNoLt_In (seq_len s) Hs (seq_len s + - P) Hidx_o Hidx_lt. }
claim Hsn_v : ValidSeq (seq_snoc s m). { exact seq_snoc_valid s Hs m. }
claim Hsn_nlt : NoLeadingTool (seq_snoc s m). { exact seq_snoc_preserves_NoLeadingTool s Hs Hspos Hnlt m. }
claim Hnge : ~(M <= seq_len (seq_snoc s m)).
{ rewrite seq_snoc_len s m.
  assume Hle : M <= seq_len s + 1.
  exact SNoLt_irref M (SNoLeLt_tra M (seq_len s + 1) M (omega_SNo M HM) (SNo_add_SNo (seq_len s) 1 (omega_SNo (seq_len s) Hs) SNo_1) (omega_SNo M HM) Hle HltM). }
claim Htrim : window_trim M R (seq_snoc s m) = seq_snoc s m.
{ exact If_i_0 (M <= seq_len (seq_snoc s m)) (seq_drop (seq_len (seq_snoc s m) + - R) (seq_snoc s m)) (seq_snoc s m) Hnge. }
claim Hcut0 : lead_tool_cut (seq_snoc s m) = 0.
{ apply lead_tool_cut_eq (seq_snoc s m) Hsn_v 0
        (nat_Le_In_ordsucc 0 nat_0_omega (seq_len (seq_snoc s m)) Hsn_v (nat_0_Le (seq_len (seq_snoc s m)) Hsn_v)).
  - let j. assume Hj. apply FalseE. exact EmptyE j Hj.
  - apply Hsn_nlt.
    + assume H0 : seq_len (seq_snoc s m) = 0. apply orIL. symmetry. exact H0.
    + assume Hne : msg_role (seq_at (seq_snoc s m) 0) <> RoleTool. apply orIR. exact Hne. }
claim Hhyg_len : seq_len (hygiene_step M R (seq_snoc s m)) = seq_len s + 1.
{ prove seq_len (drop_leading_tools (window_trim M R (seq_snoc s m))) = seq_len s + 1.
  rewrite Htrim.
  prove seq_len (Seq (seq_len (seq_snoc s m) + - lead_tool_cut (seq_snoc s m))
                     (fun i => seq_at (seq_snoc s m) (lead_tool_cut (seq_snoc s m) + i))) = seq_len s + 1.
  rewrite seq_len_mk (seq_len (seq_snoc s m) + - lead_tool_cut (seq_snoc s m))
          (fun i => seq_at (seq_snoc s m) (lead_tool_cut (seq_snoc s m) + i)).
  rewrite Hcut0. rewrite minus_SNo_0.
  rewrite add_SNo_0R (seq_len (seq_snoc s m)) (omega_SNo (seq_len (seq_snoc s m)) Hsn_v).
  exact seq_snoc_len s m. }
claim Hidx_in1 : seq_len s + - P :e seq_len s + 1.
{ rewrite <- ordsucc_eq_add_1 (seq_len s) Hs. exact ordsuccI1 (seq_len s) (seq_len s + - P) Hidx_in. }
claim Hidx_in_h : seq_len s + - P :e seq_len (hygiene_step M R (seq_snoc s m)).
{ rewrite Hhyg_len. exact Hidx_in1. }
claim Hhyg_at : seq_at (hygiene_step M R (seq_snoc s m)) (seq_len s + - P) = seq_at s (seq_len s + - P).
{ prove seq_at (drop_leading_tools (window_trim M R (seq_snoc s m))) (seq_len s + - P) = seq_at s (seq_len s + - P).
  rewrite Htrim.
  claim Hsub1 : seq_len s + - P :e seq_len (seq_snoc s m) + - lead_tool_cut (seq_snoc s m).
  { rewrite Hcut0. rewrite minus_SNo_0.
    rewrite add_SNo_0R (seq_len (seq_snoc s m)) (omega_SNo (seq_len (seq_snoc s m)) Hsn_v).
    rewrite seq_snoc_len s m. exact Hidx_in1. }
  prove seq_at (Seq (seq_len (seq_snoc s m) + - lead_tool_cut (seq_snoc s m))
                    (fun i => seq_at (seq_snoc s m) (lead_tool_cut (seq_snoc s m) + i))) (seq_len s + - P)
      = seq_at s (seq_len s + - P).
  rewrite seq_at_mk (seq_len (seq_snoc s m) + - lead_tool_cut (seq_snoc s m))
          (fun i => seq_at (seq_snoc s m) (lead_tool_cut (seq_snoc s m) + i)) (seq_len s + - P) Hsub1.
  rewrite Hcut0.
  rewrite add_SNo_0L (seq_len s + - P) (omega_SNo (seq_len s + - P) Hidx_o).
  claim Hsn_pref : PrefixOf s (seq_snoc s m). { exact seq_snoc_PrefixOf s Hs m. }
  apply Hsn_pref. assume _ Hsn_at.
  exact Hsn_at (seq_len s + - P) Hidx_in. }
claim Hlt_clean : (seq_len s + - P) + P < seq_len (hygiene_step M R (seq_snoc s m)).
{ rewrite Hhyg_len.
  rewrite add_SNo_com (seq_len s + - P) P (omega_SNo (seq_len s + - P) Hidx_o) (omega_SNo P HP).
  rewrite SNo_add_sub_L (seq_len s) P (omega_SNo (seq_len s) Hs) (omega_SNo P HP).
  rewrite <- add_SNo_0R (seq_len s) (omega_SNo (seq_len s) Hs) at 1.
  exact add_SNo_Lt2 (seq_len s) 0 1 (omega_SNo (seq_len s) Hs) SNo_0 SNo_1 SNoLt_0_1. }
claim Hnorm_at : seq_at (normalize_experience M R P (seq_snoc s m)) (seq_len s + - P) = clean_msg (seq_at s (seq_len s + - P)).
{ prove seq_at (Seq (seq_len (hygiene_step M R (seq_snoc s m)))
                    (fun i => if i + P < seq_len (hygiene_step M R (seq_snoc s m))
                              then clean_msg (seq_at (hygiene_step M R (seq_snoc s m)) i)
                              else seq_at (hygiene_step M R (seq_snoc s m)) i)) (seq_len s + - P)
      = clean_msg (seq_at s (seq_len s + - P)).
  rewrite seq_at_mk (seq_len (hygiene_step M R (seq_snoc s m)))
          (fun i => if i + P < seq_len (hygiene_step M R (seq_snoc s m))
                    then clean_msg (seq_at (hygiene_step M R (seq_snoc s m)) i)
                    else seq_at (hygiene_step M R (seq_snoc s m)) i) (seq_len s + - P) Hidx_in_h.
  rewrite If_i_1 ((seq_len s + - P) + P < seq_len (hygiene_step M R (seq_snoc s m)))
          (clean_msg (seq_at (hygiene_step M R (seq_snoc s m)) (seq_len s + - P)))
          (seq_at (hygiene_step M R (seq_snoc s m)) (seq_len s + - P)) Hlt_clean.
  rewrite Hhyg_at. reflexivity. }
apply Hpref. assume _ Hpref_at.
apply Hdirty.
rewrite <- Hnorm_at.
exact Hpref_at (seq_len s + - P) Hidx_in.
Qed.

(** CONCRETE SEPARATION WITNESS (len = 80, P = 10):
    Constructs an already-clean, ToolPaired, NoLeadingTool 80-message history
    with one verbose tool message at index 70 (80 - 10). On the very next turn
    (appending one User message, len 80 -> 81 inside bucket 4):
      - The 20-message jump cadence preserves PrefixOf identically (KV-cache hit).
      - Per-turn normalize_experience strictly breaks PrefixOf (KV-cache miss). *)
Definition cache_witness_seq : set -> set :=
  fun x => Seq RETAIN_EXP (fun i => if i = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0).

Theorem cache_prefix_separation_witness :
  CleanOpsIdempotent ->
  forall x, trunc_tool x <> x ->
  (forall y, strip_reasoning y = y) ->
  ValidSeq (cache_witness_seq x) /\
  NoLeadingTool (cache_witness_seq x) /\
  CleanedUp 10 (cache_witness_seq x) /\
  PrefixOf (cache_witness_seq x) (seq_snoc (cache_witness_seq x) (Msg RoleUser 0)) /\
  ~(PrefixOf (cache_witness_seq x) (normalize_experience MAX_EXP RETAIN_EXP 10 (seq_snoc (cache_witness_seq x) (Msg RoleUser 0)))).
assume Hidem. let x. assume Htx Hsr.
claim H10o : 10 :e omega. { exact nat_p_omega 10 nat_10. }
claim H10pos : 0 < 10. { exact nat_In_SNoLt 10 H10o 0 (nat_0_in_ordsucc 9 nat_9). }
claim H10le20 : 10 <= INTERVAL_EXP.
{ prove 10 <= 10 + 10.
  rewrite <- add_SNo_0R 10 (omega_SNo 10 H10o) at 1.
  exact add_SNo_Le2 10 0 10 (omega_SNo 10 H10o) SNo_0 (omega_SNo 10 H10o) (nat_0_Le 10 H10o). }
claim H10le80 : 10 <= RETAIN_EXP.
{ apply SNoLe_tra 10 INTERVAL_EXP RETAIN_EXP (omega_SNo 10 H10o) (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo RETAIN_EXP n80_omega) H10le20.
  rewrite n80_eq_60_plus_20.
  rewrite <- add_SNo_0L INTERVAL_EXP (omega_SNo INTERVAL_EXP n20_omega) at 1.
  exact add_SNo_Le1 0 INTERVAL_EXP (3 * INTERVAL_EXP) SNo_0 (omega_SNo INTERVAL_EXP n20_omega) (omega_SNo (3 * INTERVAL_EXP) n60_omega) (nat_0_Le (3 * INTERVAL_EXP) n60_omega). }
claim H70o : RETAIN_EXP + - 10 :e omega. { exact nat_sub_omega 10 H10o RETAIN_EXP n80_omega H10le80. }
claim H70lt80 : RETAIN_EXP + - 10 < RETAIN_EXP.
{ rewrite <- SNo_add_sub_L RETAIN_EXP 10 (omega_SNo RETAIN_EXP n80_omega) (omega_SNo 10 H10o) at 2.
  rewrite <- add_SNo_0L (RETAIN_EXP + - 10) (omega_SNo (RETAIN_EXP + - 10) H70o) at 1.
  exact add_SNo_Lt1 0 (RETAIN_EXP + - 10) 10 SNo_0 (omega_SNo (RETAIN_EXP + - 10) H70o) (omega_SNo 10 H10o) H10pos. }
claim H70in80 : RETAIN_EXP + - 10 :e RETAIN_EXP. { exact nat_SNoLt_In RETAIN_EXP n80_omega (RETAIN_EXP + - 10) H70o H70lt80. }
claim H70pos : 0 < RETAIN_EXP + - 10.
{ claim H60pos : 0 < 3 * INTERVAL_EXP.
  { exact mul_SNo_pos_pos 3 INTERVAL_EXP (omega_SNo 3 (nat_p_omega 3 nat_3)) (omega_SNo INTERVAL_EXP n20_omega)
          (nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 0 In_0_3) n20_pos. }
  exact SNoLtLe_tra 0 (3 * INTERVAL_EXP) (RETAIN_EXP + - 10) SNo_0 (omega_SNo (3 * INTERVAL_EXP) n60_omega) (omega_SNo (RETAIN_EXP + - 10) H70o)
        H60pos (retain_sub_ge_60 10 H10o H10le20). }
claim H0neq70 : 0 <> RETAIN_EXP + - 10.
{ assume Heq : 0 = RETAIN_EXP + - 10. apply SNoLt_irref 0. rewrite Heq at 2. exact H70pos. }
claim Hlen : seq_len (cache_witness_seq x) = RETAIN_EXP.
{ exact seq_len_mk RETAIN_EXP (fun i => if i = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0). }
claim Hv : ValidSeq (cache_witness_seq x).
{ exact ValidSeq_mk RETAIN_EXP n80_omega (fun i => if i = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0). }
claim H0in80 : 0 :e RETAIN_EXP.
{ exact nat_SNoLt_In RETAIN_EXP n80_omega 0 nat_0_omega (SNoLt_tra 0 (RETAIN_EXP + - 10) RETAIN_EXP SNo_0 (omega_SNo (RETAIN_EXP + - 10) H70o) (omega_SNo RETAIN_EXP n80_omega) H70pos H70lt80). }
claim Hnlt : NoLeadingTool (cache_witness_seq x).
{ prove seq_len (cache_witness_seq x) = 0 \/ msg_role (seq_at (cache_witness_seq x) 0) <> RoleTool.
  apply orIR.
  prove msg_role (seq_at (Seq RETAIN_EXP (fun i => if i = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0)) 0) <> RoleTool.
  rewrite seq_at_mk RETAIN_EXP (fun i => if i = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0) 0 H0in80.
  rewrite If_i_0 (0 = RETAIN_EXP + - 10) (Msg RoleTool x) (Msg RoleAssistant 0) H0neq70.
  rewrite msg_role_pair RoleAssistant 0.
  exact RoleAssistant_neq_Tool. }
claim Hclean : CleanedUp 10 (cache_witness_seq x).
{ let i. assume Hi Hlt.
  claim Hin : i :e RETAIN_EXP. { rewrite <- Hlen. exact Hi. }
  claim Hio : i :e omega. { exact nat_In_omega RETAIN_EXP n80_omega i Hin. }
  claim Hlt80 : i + 10 < RETAIN_EXP. { rewrite <- Hlen. exact Hlt. }
  claim Hneq70 : i <> RETAIN_EXP + - 10.
  { assume Heq : i = RETAIN_EXP + - 10.
    apply SNoLt_irref RETAIN_EXP.
    rewrite <- SNo_add_sub_L RETAIN_EXP 10 (omega_SNo RETAIN_EXP n80_omega) (omega_SNo 10 H10o) at 1.
    rewrite add_SNo_com 10 (RETAIN_EXP + - 10) (omega_SNo 10 H10o) (omega_SNo (RETAIN_EXP + - 10) H70o).
    rewrite <- Heq. exact Hlt80. }
  claim Hati : seq_at (cache_witness_seq x) i = Msg RoleAssistant 0.
  { prove seq_at (Seq RETAIN_EXP (fun j => if j = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0)) i = Msg RoleAssistant 0.
    rewrite seq_at_mk RETAIN_EXP (fun j => if j = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0) i Hin.
    exact If_i_0 (i = RETAIN_EXP + - 10) (Msg RoleTool x) (Msg RoleAssistant 0) Hneq70. }
  rewrite Hati.
  claim Hnt : msg_role (Msg RoleAssistant 0) <> RoleTool. { rewrite msg_role_pair RoleAssistant 0. exact RoleAssistant_neq_Tool. }
  claim Ha : msg_role (Msg RoleAssistant 0) = RoleAssistant. { exact msg_role_pair RoleAssistant 0. }
  prove (if msg_role (Msg RoleAssistant 0) = RoleTool then Msg RoleTool (trunc_tool (msg_content (Msg RoleAssistant 0)))
         else if msg_role (Msg RoleAssistant 0) = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleAssistant 0)))
         else if msg_role (Msg RoleAssistant 0) = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleAssistant 0)))
         else Msg RoleAssistant 0) = Msg RoleAssistant 0.
  rewrite If_i_0 (msg_role (Msg RoleAssistant 0) = RoleTool)
          (Msg RoleTool (trunc_tool (msg_content (Msg RoleAssistant 0))))
          (if msg_role (Msg RoleAssistant 0) = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleAssistant 0)))
           else if msg_role (Msg RoleAssistant 0) = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleAssistant 0)))
           else Msg RoleAssistant 0) Hnt.
  rewrite If_i_1 (msg_role (Msg RoleAssistant 0) = RoleAssistant)
          (Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleAssistant 0))))
          (if msg_role (Msg RoleAssistant 0) = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleAssistant 0)))
           else Msg RoleAssistant 0) Ha.
  rewrite msg_content_pair RoleAssistant 0.
  rewrite Hsr 0. reflexivity. }
claim H81lt100 : RETAIN_EXP + 1 < MAX_EXP.
{ rewrite n100_eq_80_plus_20.
  claim H1lt20 : 1 < INTERVAL_EXP.
  { prove 1 < 10 + 10.
    claim H1lt10 : 1 < 10.
    { apply nat_In_SNoLt 10 H10o 1.
      exact ordsuccI1 9 1 (ordsuccI1 8 1 (ordsuccI1 7 1 (ordsuccI1 6 1 (ordsuccI1 5 1 (ordsuccI1 4 1 (ordsuccI1 3 1 (ordsuccI1 2 1 In_1_2))))))). }
    apply SNoLt_tra 1 10 (10 + 10) SNo_1 (omega_SNo 10 H10o) (omega_SNo INTERVAL_EXP n20_omega) H1lt10.
    rewrite <- add_SNo_0R 10 (omega_SNo 10 H10o) at 1.
    exact add_SNo_Lt2 10 0 10 (omega_SNo 10 H10o) SNo_0 (omega_SNo 10 H10o) H10pos. }
  exact add_SNo_Lt2 RETAIN_EXP 1 INTERVAL_EXP (omega_SNo RETAIN_EXP n80_omega) SNo_1 (omega_SNo INTERVAL_EXP n20_omega) H1lt20. }
claim Hdirty : clean_msg (seq_at (cache_witness_seq x) (seq_len (cache_witness_seq x) + - 10)) <> seq_at (cache_witness_seq x) (seq_len (cache_witness_seq x) + - 10).
{ rewrite Hlen.
  claim Hat70 : seq_at (cache_witness_seq x) (RETAIN_EXP + - 10) = Msg RoleTool x.
  { prove seq_at (Seq RETAIN_EXP (fun j => if j = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0)) (RETAIN_EXP + - 10) = Msg RoleTool x.
    rewrite seq_at_mk RETAIN_EXP (fun j => if j = RETAIN_EXP + - 10 then Msg RoleTool x else Msg RoleAssistant 0) (RETAIN_EXP + - 10) H70in80.
    claim Href : RETAIN_EXP + - 10 = RETAIN_EXP + - 10. { reflexivity. }
    exact If_i_1 (RETAIN_EXP + - 10 = RETAIN_EXP + - 10) (Msg RoleTool x) (Msg RoleAssistant 0) Href. }
  rewrite Hat70.
  claim Ht : msg_role (Msg RoleTool x) = RoleTool. { exact msg_role_pair RoleTool x. }
  prove (if msg_role (Msg RoleTool x) = RoleTool then Msg RoleTool (trunc_tool (msg_content (Msg RoleTool x)))
         else if msg_role (Msg RoleTool x) = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleTool x)))
         else if msg_role (Msg RoleTool x) = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleTool x)))
         else Msg RoleTool x) <> Msg RoleTool x.
  rewrite If_i_1 (msg_role (Msg RoleTool x) = RoleTool)
          (Msg RoleTool (trunc_tool (msg_content (Msg RoleTool x))))
          (if msg_role (Msg RoleTool x) = RoleAssistant then Msg RoleAssistant (strip_reasoning (msg_content (Msg RoleTool x)))
           else if msg_role (Msg RoleTool x) = RoleRaw then Msg RoleRaw (strip_reasoning (msg_content (Msg RoleTool x)))
           else Msg RoleTool x) Ht.
  rewrite msg_content_pair RoleTool x.
  assume Heq : Msg RoleTool (trunc_tool x) = Msg RoleTool x.
  apply Htx.
  rewrite <- msg_content_pair RoleTool (trunc_tool x).
  rewrite Heq.
  exact msg_content_pair RoleTool x. }
apply andI.
- apply andI.
  + apply andI.
    * apply andI.
      { exact Hv. }
      { exact Hnlt. }
    * exact Hclean.
  + exact seq_snoc_PrefixOf (cache_witness_seq x) Hv (Msg RoleUser 0).
- apply per_turn_normalize_breaks_prefix MAX_EXP n100_omega RETAIN_EXP n80_omega n80_lt_100 10 H10o H10pos (cache_witness_seq x) Hv.
  + rewrite Hlen. exact H10le80.
  + rewrite Hlen. exact H81lt100.
  + exact Hnlt.
  + exact Hdirty.
Qed.

(** SENTINEL INITIALIZATION THEOREMS (&cleanup_bucket = -1):
    Initializing cleanup_bucket to -1 instead of floor(len / interval) causes
    Loop's existing cleanup guard (-1 < bucket20 L) to fire once on the first
    iteration for EVERY loaded history length L in omega (both L < 100 and
    L >= 100), without duplicating cleanup_old_messages or moving the orphan
    strip ahead of bucket recording. In particular, an 80-message loaded
    history with k leading orphan tools cleans once at turn 0, records
    bucket = 4 from the pre-strip length 80, strips to 80 - k, and then stays
    completely silent for all (19 + k) turns until L = 100. *)

Theorem neg1_lt_bucket20 : forall L :e omega, - 1 < bucket20 L.
let L. assume HL.
claim Hspec : IsBucket20 L (bucket20 L). { exact bucket20_spec L HL. }
apply Hspec. assume Hb1 _. apply Hb1. assume Hbo _.
exact SNoLtLe_tra (- 1) 0 (bucket20 L) (SNo_minus_SNo 1 SNo_1) SNo_0 (omega_SNo (bucket20 L) Hbo) SNoLt_minus_1_0 (nat_0_Le (bucket20 L) Hbo).
Qed.

Theorem init_bucket_neg1_fires_on_any_startup :
  forall policy k, forall L :e omega,
  cad_count (cad_step policy k (CadState L (- 1) 0)) = 1 /\
  (L < MAX_EXP -> cad_bucket (cad_step policy k (CadState L (- 1) 0)) = bucket20 L) /\
  (MAX_EXP <= L -> policy = PolicyPreStrip -> cad_bucket (cad_step policy k (CadState L (- 1) 0)) = 4).
let policy k. let L. assume HL.
claim Hlt : - 1 < bucket20 L. { exact neg1_lt_bucket20 L HL. }
claim Hnc : cad_next_count L (- 1) 0 = 1.
{ prove (if - 1 < bucket20 L then 0 + 1 else 0) = 1.
  rewrite If_i_1 (- 1 < bucket20 L) (0 + 1) 0 Hlt.
  exact add_SNo_0L 1 SNo_1. }
apply and3I.
- prove cad_count (CadState (cad_next_len k (cad_len (CadState L (- 1) 0)))
                            (cad_next_bucket policy k (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)))
                            (cad_next_count (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)) (cad_count (CadState L (- 1) 0)))) = 1.
  rewrite cad_count_mk (cad_next_len k (cad_len (CadState L (- 1) 0)))
          (cad_next_bucket policy k (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)))
          (cad_next_count (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)) (cad_count (CadState L (- 1) 0))).
  rewrite cad_len_mk L (- 1) 0.
  rewrite cad_bucket_mk L (- 1) 0.
  rewrite cad_count_mk L (- 1) 0.
  exact Hnc.
- assume Hlt100 : L < MAX_EXP.
  claim Hnle : ~(MAX_EXP <= L).
  { assume Hle : MAX_EXP <= L.
    exact SNoLt_irref L (SNoLtLe_tra L MAX_EXP L (omega_SNo L HL) (omega_SNo MAX_EXP n100_omega) (omega_SNo L HL) Hlt100 Hle). }
  prove cad_bucket (CadState (cad_next_len k (cad_len (CadState L (- 1) 0)))
                             (cad_next_bucket policy k (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)))
                             (cad_next_count (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)) (cad_count (CadState L (- 1) 0)))) = bucket20 L.
  rewrite cad_bucket_mk (cad_next_len k (cad_len (CadState L (- 1) 0)))
          (cad_next_bucket policy k (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)))
          (cad_next_count (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)) (cad_count (CadState L (- 1) 0))).
  rewrite cad_len_mk L (- 1) 0.
  rewrite cad_bucket_mk L (- 1) 0.
  prove (if MAX_EXP <= L then
           (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
         else
           (if - 1 < bucket20 L then bucket20 L else - 1)) = bucket20 L.
  rewrite If_i_0 (MAX_EXP <= L)
          (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
          (if - 1 < bucket20 L then bucket20 L else - 1) Hnle.
  exact If_i_1 (- 1 < bucket20 L) (bucket20 L) (- 1) Hlt.
- assume Hge100 : MAX_EXP <= L. assume Hpol : policy = PolicyPreStrip.
  prove cad_bucket (CadState (cad_next_len k (cad_len (CadState L (- 1) 0)))
                             (cad_next_bucket policy k (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)))
                             (cad_next_count (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)) (cad_count (CadState L (- 1) 0)))) = 4.
  rewrite cad_bucket_mk (cad_next_len k (cad_len (CadState L (- 1) 0)))
          (cad_next_bucket policy k (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)))
          (cad_next_count (cad_len (CadState L (- 1) 0)) (cad_bucket (CadState L (- 1) 0)) (cad_count (CadState L (- 1) 0))).
  rewrite cad_len_mk L (- 1) 0.
  rewrite cad_bucket_mk L (- 1) 0.
  prove (if MAX_EXP <= L then
           (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
         else
           (if - 1 < bucket20 L then bucket20 L else - 1)) = 4.
  rewrite If_i_1 (MAX_EXP <= L)
          (if policy = PolicyPreStrip then bucket20 RETAIN_EXP else bucket20 (RETAIN_EXP + - k))
          (if - 1 < bucket20 L then bucket20 L else - 1) Hge100.
  rewrite If_i_1 (policy = PolicyPreStrip) (bucket20 RETAIN_EXP) (bucket20 (RETAIN_EXP + - k)) Hpol.
  exact bucket20_80_to_99 RETAIN_EXP n80_omega (SNoLe_ref RETAIN_EXP) n80_lt_100.
Qed.

Theorem init_bucket_neg1_orphan80_stays_uniform :
  forall k :e omega, k <= RETAIN_EXP ->
  cad_count (cad_step PolicyPreStrip k (CadState RETAIN_EXP (- 1) 0)) = 1 /\
  cad_bucket (cad_step PolicyPreStrip k (CadState RETAIN_EXP (- 1) 0)) = 4 /\
  cad_run PolicyPreStrip k (CadState ((RETAIN_EXP + - k) + 1) 4 1) ((10 + 9) + k) = CadState MAX_EXP 4 1.
let k. assume Hk Hk80.
claim Hst : cad_count (cad_step PolicyPreStrip k (CadState RETAIN_EXP (- 1) 0)) = 1 /\
  (RETAIN_EXP < MAX_EXP -> cad_bucket (cad_step PolicyPreStrip k (CadState RETAIN_EXP (- 1) 0)) = bucket20 RETAIN_EXP) /\
  (MAX_EXP <= RETAIN_EXP -> PolicyPreStrip = PolicyPreStrip -> cad_bucket (cad_step PolicyPreStrip k (CadState RETAIN_EXP (- 1) 0)) = 4).
{ exact init_bucket_neg1_fires_on_any_startup PolicyPreStrip k RETAIN_EXP n80_omega. }
apply Hst. assume H12 _. apply H12. assume Hc Hb.
apply and3I.
- exact Hc.
- rewrite Hb n80_lt_100.
  exact bucket20_80_to_99 RETAIN_EXP n80_omega (SNoLe_ref RETAIN_EXP) n80_lt_100.
- exact original_silent_stretch_all_k k Hk Hk80 1 nat_1_omega.
Qed.

End IterExperienceHygiene.
