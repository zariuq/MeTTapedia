(** ============================================================================
   Iter Native MeTTa Architecture Verification - Module 5
   Upstream Extensions (f4064d9..774f805):
     1. Parametric Configurable Experience Window & Cleanup Interval (R < M)
     2. Resource Caps (MAX_TOOLS, MAX_SKILLS, MAX_CONTEXT_TRANSFORMATIONS)
     3. Markdown Skill Indexing Hygiene
     4. LLM_BACKUP_MODEL Refusal & Error Fallback State Machine
   Checked natively by CeTTa's Megalodon kernel against standard Egal preamble.mgs.
   Zero document axioms. Zero admitted. Zero aby.
   ============================================================================ *)

Section IterUpstreamExtensions.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.

(** ---- Part 1: Natural Arithmetic Helpers on omega ------------------------- *)

Theorem u_nat_0_omega : 0 :e omega.
exact nat_p_omega 0 nat_0.
Qed.

Theorem u_nat_1_omega : 1 :e omega.
exact nat_p_omega 1 nat_1.
Qed.

Theorem u_nat_2_omega : 2 :e omega.
exact nat_p_omega 2 nat_2.
Qed.

Theorem u_nat_add_omega : forall n :e omega, forall m :e omega, n + m :e omega.
let n. assume Hn. let m. assume Hm.
rewrite <- add_nat_add_SNo n Hn m Hm.
exact nat_p_omega (add_nat n m) (add_nat_p n (omega_nat_p n Hn) m (omega_nat_p m Hm)).
Qed.

Theorem u_nat_mul_omega : forall n :e omega, forall m :e omega, n * m :e omega.
let n. assume Hn. let m. assume Hm.
rewrite <- mul_nat_mul_SNo n Hn m Hm.
exact nat_p_omega (mul_nat n m) (mul_nat_p n (omega_nat_p n Hn) m (omega_nat_p m Hm)).
Qed.

Theorem u_ordsucc_eq_add_1 : forall n :e omega, ordsucc n = n + 1.
let n. assume Hn.
rewrite <- add_nat_add_SNo n Hn 1 u_nat_1_omega.
prove ordsucc n = add_nat n (ordsucc 0).
rewrite add_nat_SR n 0 nat_0.
rewrite add_nat_0R n.
reflexivity.
Qed.

Theorem u_nat_In_SNoLt : forall n :e omega, forall m :e n, m < n.
let n. assume Hn. let m. assume Hm.
exact ordinal_In_SNoLt n (nat_p_ordinal n (omega_nat_p n Hn)) m Hm.
Qed.

Theorem u_nat_SNoLt_In : forall n :e omega, forall m :e omega, m < n -> m :e n.
let n. assume Hn. let m. assume Hm. assume Hlt.
apply ordinal_trichotomy_or_impred m n (nat_p_ordinal m (omega_nat_p m Hm)) (nat_p_ordinal n (omega_nat_p n Hn)).
- assume H : m :e n. exact H.
- assume Heq : m = n. apply FalseE. apply SNoLt_irref m. rewrite Heq at 2. exact Hlt.
- assume Hrev : n :e m.
  apply FalseE.
  exact SNoLt_irref m (SNoLt_tra m n m (omega_SNo m Hm) (omega_SNo n Hn) (omega_SNo m Hm) Hlt (u_nat_In_SNoLt m Hm n Hrev)).
Qed.

Theorem u_nat_SNoLe_cases : forall m :e omega, forall n :e omega, m <= n -> m :e n \/ m = n.
let m. assume Hm. let n. assume Hn. assume Hle.
apply ordinal_trichotomy_or_impred m n (nat_p_ordinal m (omega_nat_p m Hm)) (nat_p_ordinal n (omega_nat_p n Hn)).
- assume H : m :e n. exact orIL (m :e n) (m = n) H.
- assume H : m = n. exact orIR (m :e n) (m = n) H.
- assume Hrev : n :e m.
  apply FalseE.
  exact SNoLt_irref n (SNoLtLe_tra n m n (omega_SNo n Hn) (omega_SNo m Hm) (omega_SNo n Hn) (u_nat_In_SNoLt m Hm n Hrev) Hle).
Qed.

Theorem u_nat_0_Le : forall n :e omega, 0 <= n.
let n. assume Hn.
apply nat_ind (fun k => 0 <= k).
- exact SNoLe_ref 0.
- let k. assume Hk Hle.
  claim Hko : k :e omega. { exact nat_p_omega k Hk. }
  rewrite u_ordsucc_eq_add_1 k Hko.
  apply SNoLe_tra 0 k (k + 1) SNo_0 (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) Hle.
  rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
  exact add_SNo_Le2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
- exact omega_nat_p n Hn.
Qed.

Theorem u_nat_In_ordsucc_Le : forall n :e omega, forall m :e ordsucc n, m <= n.
let n. assume Hn. let m. assume Hm.
apply ordsuccE n m Hm.
- assume Hin : m :e n. exact SNoLtLe m n (u_nat_In_SNoLt n Hn m Hin).
- assume Heq : m = n. rewrite Heq. exact SNoLe_ref n.
Qed.

Theorem u_nat_pos_pred : forall n :e omega, 0 < n -> exists k :e omega, n = k + 1.
let n. assume Hn Hpos.
apply nat_inv n (omega_nat_p n Hn).
- assume H0 : n = 0. apply FalseE. apply SNoLt_irref 0. rewrite <- H0 at 2. exact Hpos.
- assume Hex. apply Hex. let k. assume Hk. apply Hk. assume Hkn Heq.
  claim Hko : k :e omega. { exact nat_p_omega k Hkn. }
  witness k. apply andI.
  + exact Hko.
  + rewrite Heq. exact u_ordsucc_eq_add_1 k Hko.
Qed.

Theorem u_nat_SNoLt_S_Le : forall m :e omega, forall n :e omega, m < n -> m + 1 <= n.
let m. assume Hm. let n. assume Hn Hlt.
claim Hin : m :e n. { exact u_nat_SNoLt_In n Hn m Hm Hlt. }
claim Hnpos : 0 < n. { exact SNoLeLt_tra 0 m n SNo_0 (omega_SNo m Hm) (omega_SNo n Hn) (u_nat_0_Le m Hm) Hlt. }
apply u_nat_pos_pred n Hn Hnpos. let k. assume Hk. apply Hk. assume Hko Heq.
claim Hmk : m :e ordsucc k. { rewrite u_ordsucc_eq_add_1 k Hko. rewrite <- Heq. exact Hin. }
rewrite Heq.
exact add_SNo_Le1 m 1 k (omega_SNo m Hm) SNo_1 (omega_SNo k Hko) (u_nat_In_ordsucc_Le k Hko m Hmk).
Qed.

Theorem u_SNo_add_sub_L : forall a b, SNo a -> SNo b -> b + (a + - b) = a.
let a b. assume Ha Hb.
rewrite add_SNo_com a (- b) Ha (SNo_minus_SNo b Hb).
rewrite add_SNo_assoc b (- b) a Hb (SNo_minus_SNo b Hb) Ha.
rewrite add_SNo_minus_SNo_rinv b Hb.
exact add_SNo_0L a Ha.
Qed.

Theorem u_SNo_add_sub_cancel_1 : forall k m, SNo k -> SNo m -> (k + 1) + - (m + 1) = k + - m.
let k m. assume Hk Hm.
rewrite minus_add_SNo_distr m 1 Hm SNo_1.
rewrite add_SNo_com (- m) (- 1) (SNo_minus_SNo m Hm) (SNo_minus_SNo 1 SNo_1).
rewrite add_SNo_assoc (k + 1) (- 1) (- m) (SNo_add_SNo k 1 Hk SNo_1) (SNo_minus_SNo 1 SNo_1) (SNo_minus_SNo m Hm).
rewrite add_SNo_minus_R2 k 1 Hk SNo_1.
reflexivity.
Qed.

Theorem u_nat_sub_omega : forall m :e omega, forall n :e omega, m <= n -> n + - m :e omega.
let m. assume Hm.
apply nat_ind (fun k => forall n :e omega, k <= n -> n + - k :e omega).
- let n. assume Hn _. rewrite minus_SNo_0. rewrite add_SNo_0R n (omega_SNo n Hn). exact Hn.
- let k. assume Hk IH. let n. assume Hn Hle.
  claim Hko : k :e omega. { exact nat_p_omega k Hk. }
  claim Hk1 : ordsucc k = k + 1. { exact u_ordsucc_eq_add_1 k Hko. }
  claim Hnpos : 0 < n.
  { apply SNoLtLe_tra 0 (k + 1) n SNo_0 (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) (omega_SNo n Hn).
    - apply SNoLeLt_tra 0 k (k + 1) SNo_0 (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) (u_nat_0_Le k Hko).
      rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
      exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1.
    - rewrite <- Hk1. exact Hle. }
  apply u_nat_pos_pred n Hn Hnpos. let p. assume Hp. apply Hp. assume Hpo Hnp.
  claim Hkp : k <= p.
  { apply ordinal_trichotomy_or_impred k p (nat_p_ordinal k Hk) (nat_p_ordinal p (omega_nat_p p Hpo)).
    - assume H1 : k :e p. exact SNoLtLe k p (u_nat_In_SNoLt p Hpo k H1).
    - assume H1 : k = p. rewrite H1. exact SNoLe_ref p.
    - assume H1 : p :e k.
      apply FalseE.
      claim Hpk : p + 1 <= k. { exact u_nat_SNoLt_S_Le p Hpo k Hko (u_nat_In_SNoLt k Hko p H1). }
      claim Hnk : n < ordsucc k.
      { rewrite Hnp. rewrite Hk1.
        apply SNoLeLt_tra (p + 1) k (k + 1) (SNo_add_SNo p 1 (omega_SNo p Hpo) SNo_1) (omega_SNo k Hko) (SNo_add_SNo k 1 (omega_SNo k Hko) SNo_1) Hpk.
        rewrite <- add_SNo_0R k (omega_SNo k Hko) at 1.
        exact add_SNo_Lt2 k 0 1 (omega_SNo k Hko) SNo_0 SNo_1 SNoLt_0_1. }
      exact SNoLt_irref n (SNoLtLe_tra n (ordsucc k) n (omega_SNo n Hn) (omega_SNo (ordsucc k) (omega_ordsucc k Hko)) (omega_SNo n Hn) Hnk Hle). }
  rewrite Hnp. rewrite Hk1.
  rewrite u_SNo_add_sub_cancel_1 p k (omega_SNo p Hpo) (omega_SNo k Hko).
  exact IH p Hpo Hkp.
- exact omega_nat_p m Hm.
Qed.

Theorem u_nat_mul_mono_L : forall I :e omega, forall a :e omega, forall b :e omega, a <= b -> a * I <= b * I.
let I. assume HI. let a. assume Ha. let b. assume Hb Hle.
claim Hd_o : b + - a :e omega. { exact u_nat_sub_omega a Ha b Hb Hle. }
claim Hdeq : b = a + (b + - a). { symmetry. exact u_SNo_add_sub_L b a (omega_SNo b Hb) (omega_SNo a Ha). }
claim Hprod_nn : 0 <= (b + - a) * I. { exact u_nat_0_Le ((b + - a) * I) (u_nat_mul_omega (b + - a) Hd_o I HI). }
rewrite Hdeq.
rewrite mul_SNo_distrR a (b + - a) I (omega_SNo a Ha) (omega_SNo (b + - a) Hd_o) (omega_SNo I HI).
rewrite <- add_SNo_0R (a * I) (omega_SNo (a * I) (u_nat_mul_omega a Ha I HI)) at 1.
exact add_SNo_Le2 (a * I) 0 ((b + - a) * I)
      (omega_SNo (a * I) (u_nat_mul_omega a Ha I HI)) SNo_0
      (omega_SNo ((b + - a) * I) (u_nat_mul_omega (b + - a) Hd_o I HI)) Hprod_nn.
Qed.

(** ---- Group 1: Parametric Configurable Window & Cleanup Interval ---------- *)

Definition cfg_interval : set -> set -> set := fun M R => M + - R.

Theorem cfg_interval_omega_pos : forall M :e omega, forall R :e omega, R < M ->
  cfg_interval M R :e omega /\ 0 < cfg_interval M R.
let M. assume HM. let R. assume HR HRM.
claim Hio : M + - R :e omega. { exact u_nat_sub_omega R HR M HM (SNoLtLe R M HRM). }
prove M + - R :e omega /\ 0 < M + - R.
apply andI.
- exact Hio.
- apply add_SNo_Lt2_cancel R 0 (M + - R) (omega_SNo R HR) SNo_0 (omega_SNo (M + - R) Hio).
  rewrite add_SNo_0R R (omega_SNo R HR).
  rewrite u_SNo_add_sub_L M R (omega_SNo M HM) (omega_SNo R HR).
  exact HRM.
Qed.

Definition IsBucketGen : set -> set -> set -> prop :=
  fun I L b => b :e omega /\ b * I <= L /\ L < (b + 1) * I.

Theorem IsBucketGen_unique : forall I :e omega, 0 < I -> forall L :e omega,
  forall b1 b2, IsBucketGen I L b1 -> IsBucketGen I L b2 -> b1 = b2.
let I. assume HI HIpos. let L. assume HL. let b1 b2. assume Hb1 Hb2.
apply Hb1. assume H1a H1lt. apply H1a. assume Hb1o H1le.
apply Hb2. assume H2a H2lt. apply H2a. assume Hb2o H2le.
apply ordinal_trichotomy_or_impred b1 b2 (nat_p_ordinal b1 (omega_nat_p b1 Hb1o)) (nat_p_ordinal b2 (omega_nat_p b2 Hb2o)).
- assume H12 : b1 :e b2.
  apply FalseE.
  claim Hle12 : b1 + 1 <= b2. { exact u_nat_SNoLt_S_Le b1 Hb1o b2 Hb2o (u_nat_In_SNoLt b2 Hb2o b1 H12). }
  claim Hm12 : (b1 + 1) * I <= b2 * I. { exact u_nat_mul_mono_L I HI (b1 + 1) (u_nat_add_omega b1 Hb1o 1 u_nat_1_omega) b2 Hb2o Hle12. }
  claim HLle : (b1 + 1) * I <= L.
  { exact SNoLe_tra ((b1 + 1) * I) (b2 * I) L
          (omega_SNo ((b1 + 1) * I) (u_nat_mul_omega (b1 + 1) (u_nat_add_omega b1 Hb1o 1 u_nat_1_omega) I HI))
          (omega_SNo (b2 * I) (u_nat_mul_omega b2 Hb2o I HI)) (omega_SNo L HL) Hm12 H2le. }
  exact SNoLt_irref L (SNoLtLe_tra L ((b1 + 1) * I) L (omega_SNo L HL)
        (omega_SNo ((b1 + 1) * I) (u_nat_mul_omega (b1 + 1) (u_nat_add_omega b1 Hb1o 1 u_nat_1_omega) I HI)) (omega_SNo L HL) H1lt HLle).
- assume Heq : b1 = b2. exact Heq.
- assume H21 : b2 :e b1.
  apply FalseE.
  claim Hle21 : b2 + 1 <= b1. { exact u_nat_SNoLt_S_Le b2 Hb2o b1 Hb1o (u_nat_In_SNoLt b1 Hb1o b2 H21). }
  claim Hm21 : (b2 + 1) * I <= b1 * I. { exact u_nat_mul_mono_L I HI (b2 + 1) (u_nat_add_omega b2 Hb2o 1 u_nat_1_omega) b1 Hb1o Hle21. }
  claim HLle : (b2 + 1) * I <= L.
  { exact SNoLe_tra ((b2 + 1) * I) (b1 * I) L
          (omega_SNo ((b2 + 1) * I) (u_nat_mul_omega (b2 + 1) (u_nat_add_omega b2 Hb2o 1 u_nat_1_omega) I HI))
          (omega_SNo (b1 * I) (u_nat_mul_omega b1 Hb1o I HI)) (omega_SNo L HL) Hm21 H1le. }
  exact SNoLt_irref L (SNoLtLe_tra L ((b2 + 1) * I) L (omega_SNo L HL)
        (omega_SNo ((b2 + 1) * I) (u_nat_mul_omega (b2 + 1) (u_nat_add_omega b2 Hb2o 1 u_nat_1_omega) I HI)) (omega_SNo L HL) H2lt HLle).
Qed.

Theorem IsBucketGen_exists : forall I :e omega, 0 < I -> forall L :e omega, exists b, IsBucketGen I L b.
let I. assume HI HIpos. let L. assume HL.
apply nat_ind (fun m => exists b, IsBucketGen I m b).
- prove exists b, IsBucketGen I 0 b.
  witness 0.
  prove 0 :e omega /\ 0 * I <= 0 /\ 0 < (0 + 1) * I.
  rewrite mul_SNo_zeroL I (omega_SNo I HI).
  rewrite add_SNo_0L 1 SNo_1.
  rewrite mul_SNo_oneL I (omega_SNo I HI).
  apply and3I.
  + exact u_nat_0_omega.
  + exact SNoLe_ref 0.
  + exact HIpos.
- let m. assume Hm IH.
  claim Hmo : m :e omega. { exact nat_p_omega m Hm. }
  apply IH. let b. assume Hb. apply Hb. assume Hb1 Hmlt. apply Hb1. assume Hbo Hble.
  claim Hb1o : b + 1 :e omega. { exact u_nat_add_omega b Hbo 1 u_nat_1_omega. }
  claim Hbm1o : (b + 1) * I :e omega. { exact u_nat_mul_omega (b + 1) Hb1o I HI. }
  claim Hm1o : m + 1 :e omega. { exact u_nat_add_omega m Hmo 1 u_nat_1_omega. }
  claim Hle_succ : m + 1 <= (b + 1) * I. { exact u_nat_SNoLt_S_Le m Hmo ((b + 1) * I) Hbm1o Hmlt. }
  prove exists b', IsBucketGen I (ordsucc m) b'.
  rewrite u_ordsucc_eq_add_1 m Hmo.
  apply u_nat_SNoLe_cases (m + 1) Hm1o ((b + 1) * I) Hbm1o Hle_succ.
  + assume Hin : m + 1 :e (b + 1) * I.
    witness b.
    prove b :e omega /\ b * I <= m + 1 /\ m + 1 < (b + 1) * I.
    apply and3I.
    * exact Hbo.
    * apply SNoLe_tra (b * I) m (m + 1) (omega_SNo (b * I) (u_nat_mul_omega b Hbo I HI)) (omega_SNo m Hmo) (omega_SNo (m + 1) Hm1o) Hble.
      rewrite <- add_SNo_0R m (omega_SNo m Hmo) at 1.
      exact add_SNo_Le2 m 0 1 (omega_SNo m Hmo) SNo_0 SNo_1 (SNoLtLe 0 1 SNoLt_0_1).
    * exact u_nat_In_SNoLt ((b + 1) * I) Hbm1o (m + 1) Hin.
  + assume Heq : m + 1 = (b + 1) * I.
    witness (b + 1).
    prove b + 1 :e omega /\ (b + 1) * I <= m + 1 /\ m + 1 < ((b + 1) + 1) * I.
    apply and3I.
    * exact Hb1o.
    * rewrite Heq. exact SNoLe_ref ((b + 1) * I).
    * rewrite Heq.
      rewrite mul_SNo_distrR (b + 1) 1 I (omega_SNo (b + 1) Hb1o) SNo_1 (omega_SNo I HI).
      rewrite mul_SNo_oneL I (omega_SNo I HI).
      rewrite <- add_SNo_0R ((b + 1) * I) (omega_SNo ((b + 1) * I) Hbm1o) at 1.
      exact add_SNo_Lt2 ((b + 1) * I) 0 I (omega_SNo ((b + 1) * I) Hbm1o) SNo_0 (omega_SNo I HI) HIpos.
- exact omega_nat_p L HL.
Qed.

Definition bucket_gen : set -> set -> set := fun I L => Eps_i (fun b => IsBucketGen I L b).

Theorem bucket_gen_spec : forall I :e omega, 0 < I -> forall L :e omega, IsBucketGen I L (bucket_gen I L).
let I. assume HI HIpos. let L. assume HL.
exact Eps_i_ex (fun b => IsBucketGen I L b) (IsBucketGen_exists I HI HIpos L HL).
Qed.

Theorem bucket_gen_eq : forall I :e omega, 0 < I -> forall L :e omega, forall b, IsBucketGen I L b -> bucket_gen I L = b.
let I. assume HI HIpos. let L. assume HL. let b. assume Hb.
exact IsBucketGen_unique I HI HIpos L HL (bucket_gen I L) b (bucket_gen_spec I HI HIpos L HL) Hb.
Qed.

(** GENERAL PARAMETRIC WINDOW THEOREM:
    For EVERY valid configurable pair (M, R) with R < M and I = M - R:
      1. The -1 startup sentinel fires on turn 0 for ALL loaded lengths L :e omega.
      2. Reaching MAX_EXPERIENCE_SIZE ALWAYS advances the bucket by exactly 1
         above the retained bucket: bucket_gen I M = bucket_gen I R + 1,
         guaranteeing cleanup fires at M even when I does not divide R. *)
Theorem configurable_window_sentinel_and_step :
  forall M :e omega, forall R :e omega, R < M ->
  (forall L :e omega, - 1 < bucket_gen (cfg_interval M R) L) /\
  bucket_gen (cfg_interval M R) M = bucket_gen (cfg_interval M R) R + 1 /\
  bucket_gen (cfg_interval M R) R < bucket_gen (cfg_interval M R) M.
let M. assume HM. let R. assume HR HRM.
claim HIboth : cfg_interval M R :e omega /\ 0 < cfg_interval M R.
{ exact cfg_interval_omega_pos M HM R HR HRM. }
apply HIboth. assume HI HIpos.
claim Hbr : IsBucketGen (cfg_interval M R) R (bucket_gen (cfg_interval M R) R).
{ exact bucket_gen_spec (cfg_interval M R) HI HIpos R HR. }
apply Hbr. assume Hbr1 Hbrlt. apply Hbr1. assume Hbro Hbrle.
claim Hb1o : bucket_gen (cfg_interval M R) R + 1 :e omega. { exact u_nat_add_omega (bucket_gen (cfg_interval M R) R) Hbro 1 u_nat_1_omega. }
claim HsumM : R + cfg_interval M R = M. { exact u_SNo_add_sub_L M R (omega_SNo M HM) (omega_SNo R HR). }
claim Hbm_eq : bucket_gen (cfg_interval M R) M = bucket_gen (cfg_interval M R) R + 1.
{ apply bucket_gen_eq (cfg_interval M R) HI HIpos M HM (bucket_gen (cfg_interval M R) R + 1).
  prove bucket_gen (cfg_interval M R) R + 1 :e omega /\
        (bucket_gen (cfg_interval M R) R + 1) * cfg_interval M R <= M /\
        M < ((bucket_gen (cfg_interval M R) R + 1) + 1) * cfg_interval M R.
  apply and3I.
  - exact Hb1o.
  - rewrite mul_SNo_distrR (bucket_gen (cfg_interval M R) R) 1 (cfg_interval M R) (omega_SNo (bucket_gen (cfg_interval M R) R) Hbro) SNo_1 (omega_SNo (cfg_interval M R) HI).
    rewrite mul_SNo_oneL (cfg_interval M R) (omega_SNo (cfg_interval M R) HI).
    rewrite <- HsumM at 4.
    exact add_SNo_Le1 (bucket_gen (cfg_interval M R) R * cfg_interval M R) (cfg_interval M R) R
          (omega_SNo (bucket_gen (cfg_interval M R) R * cfg_interval M R) (u_nat_mul_omega (bucket_gen (cfg_interval M R) R) Hbro (cfg_interval M R) HI))
          (omega_SNo (cfg_interval M R) HI) (omega_SNo R HR) Hbrle.
  - rewrite mul_SNo_distrR (bucket_gen (cfg_interval M R) R + 1) 1 (cfg_interval M R) (omega_SNo (bucket_gen (cfg_interval M R) R + 1) Hb1o) SNo_1 (omega_SNo (cfg_interval M R) HI).
    rewrite mul_SNo_oneL (cfg_interval M R) (omega_SNo (cfg_interval M R) HI).
    rewrite <- HsumM at 1.
    exact add_SNo_Lt1 R (cfg_interval M R) ((bucket_gen (cfg_interval M R) R + 1) * cfg_interval M R)
          (omega_SNo R HR) (omega_SNo (cfg_interval M R) HI)
          (omega_SNo ((bucket_gen (cfg_interval M R) R + 1) * cfg_interval M R) (u_nat_mul_omega (bucket_gen (cfg_interval M R) R + 1) Hb1o (cfg_interval M R) HI)) Hbrlt. }
apply and3I.
- let L. assume HL.
  claim Hbl : IsBucketGen (cfg_interval M R) L (bucket_gen (cfg_interval M R) L).
  { exact bucket_gen_spec (cfg_interval M R) HI HIpos L HL. }
  apply Hbl. assume Hbl1 _. apply Hbl1. assume Hblo _.
  exact SNoLtLe_tra (- 1) 0 (bucket_gen (cfg_interval M R) L) (SNo_minus_SNo 1 SNo_1) SNo_0 (omega_SNo (bucket_gen (cfg_interval M R) L) Hblo) SNoLt_minus_1_0 (u_nat_0_Le (bucket_gen (cfg_interval M R) L) Hblo).
- exact Hbm_eq.
- rewrite Hbm_eq.
  rewrite <- add_SNo_0R (bucket_gen (cfg_interval M R) R) (omega_SNo (bucket_gen (cfg_interval M R) R) Hbro) at 1.
  exact add_SNo_Lt2 (bucket_gen (cfg_interval M R) R) 0 1 (omega_SNo (bucket_gen (cfg_interval M R) R) Hbro) SNo_0 SNo_1 SNoLt_0_1.
Qed.

(** ---- Group 2: Resource Caps (MAX_TOOLS, MAX_SKILLS, MAX_CONTEXT_TRANSFORMATIONS) *)

Definition cap_active : set -> set -> set := fun N C => if C <= N then C else N.
Definition cap_omitted : set -> set -> set := fun N C => if C <= N then N + - C else 0.

Theorem cap_bounds_and_conservation :
  forall N :e omega, forall C :e omega,
  cap_active N C :e omega /\
  cap_omitted N C :e omega /\
  cap_active N C <= C /\
  cap_active N C <= N /\
  cap_active N C + cap_omitted N C = N.
let N. assume HN. let C. assume HC.
apply xm (C <= N).
- assume Hle : C <= N.
  claim Ha : cap_active N C = C. { exact If_i_1 (C <= N) C N Hle. }
  claim Ho : cap_omitted N C = N + - C. { exact If_i_1 (C <= N) (N + - C) 0 Hle. }
  rewrite Ha. rewrite Ho.
  apply andI.
  + apply andI.
    * apply andI.
      { apply andI.
        - exact HC.
        - exact u_nat_sub_omega C HC N HN Hle. }
      { exact SNoLe_ref C. }
    * exact Hle.
  + exact u_SNo_add_sub_L N C (omega_SNo N HN) (omega_SNo C HC).
- assume Hnle : ~(C <= N).
  claim Hlt : N < C.
  { apply SNoLtLe_or N C (omega_SNo N HN) (omega_SNo C HC).
    - assume H : N < C. exact H.
    - assume H : C <= N. apply FalseE. exact Hnle H. }
  claim Ha : cap_active N C = N. { exact If_i_0 (C <= N) C N Hnle. }
  claim Ho : cap_omitted N C = 0. { exact If_i_0 (C <= N) (N + - C) 0 Hnle. }
  rewrite Ha. rewrite Ho.
  apply andI.
  + apply andI.
    * apply andI.
      { apply andI.
        - exact HN.
        - exact u_nat_0_omega. }
      { exact SNoLtLe N C Hlt. }
    * exact SNoLe_ref N.
  + exact add_SNo_0R N (omega_SNo N HN).
Qed.

Theorem cap_omitted_pos_iff :
  forall N :e omega, forall C :e omega,
  (0 < cap_omitted N C <-> C < N).
let N. assume HN. let C. assume HC.
apply iffI.
- assume Hpos : 0 < cap_omitted N C.
  apply xm (C <= N).
  + assume Hle : C <= N.
    claim Ho : cap_omitted N C = N + - C. { exact If_i_1 (C <= N) (N + - C) 0 Hle. }
    claim Hpos' : 0 < N + - C. { rewrite <- Ho. exact Hpos. }
    rewrite <- u_SNo_add_sub_L N C (omega_SNo N HN) (omega_SNo C HC).
    rewrite <- add_SNo_0R C (omega_SNo C HC) at 1.
    exact add_SNo_Lt2 C 0 (N + - C) (omega_SNo C HC) SNo_0 (omega_SNo (N + - C) (u_nat_sub_omega C HC N HN Hle)) Hpos'.
  + assume Hnle : ~(C <= N).
    claim Ho : cap_omitted N C = 0. { exact If_i_0 (C <= N) (N + - C) 0 Hnle. }
    apply FalseE. apply SNoLt_irref 0. rewrite <- Ho at 2. exact Hpos.
- assume Hlt : C < N.
  claim Hle : C <= N. { exact SNoLtLe C N Hlt. }
  claim Ho : cap_omitted N C = N + - C. { exact If_i_1 (C <= N) (N + - C) 0 Hle. }
  rewrite Ho.
  apply add_SNo_Lt2_cancel C 0 (N + - C) (omega_SNo C HC) SNo_0 (omega_SNo (N + - C) (u_nat_sub_omega C HC N HN Hle)).
  rewrite add_SNo_0R C (omega_SNo C HC).
  rewrite u_SNo_add_sub_L N C (omega_SNo N HN) (omega_SNo C HC).
  exact Hlt.
Qed.

Theorem cap_omitted_zero_iff :
  forall N :e omega, forall C :e omega,
  (cap_omitted N C = 0 <-> N <= C).
let N. assume HN. let C. assume HC.
apply iffI.
- assume Hz : cap_omitted N C = 0.
  apply SNoLtLe_or C N (omega_SNo C HC) (omega_SNo N HN).
  + assume Hlt : C < N.
    apply FalseE.
    claim Hpos : 0 < cap_omitted N C. { exact andER (0 < cap_omitted N C -> C < N) (C < N -> 0 < cap_omitted N C) (cap_omitted_pos_iff N HN C HC) Hlt. }
    apply SNoLt_irref 0. rewrite <- Hz at 2. exact Hpos.
  + assume Hle : N <= C. exact Hle.
- assume Hle : N <= C.
  apply u_nat_SNoLe_cases N HN C HC Hle.
  + assume Hin : N :e C.
    claim Hnle : ~(C <= N).
    { assume H : C <= N. exact SNoLt_irref N (SNoLtLe_tra N C N (omega_SNo N HN) (omega_SNo C HC) (omega_SNo N HN) (u_nat_In_SNoLt C HC N Hin) H). }
    exact If_i_0 (C <= N) (N + - C) 0 Hnle.
  + assume Heq : N = C.
    rewrite Heq.
    prove (if C <= C then C + - C else 0) = 0.
    rewrite If_i_1 (C <= C) (C + - C) 0 (SNoLe_ref C).
    exact add_SNo_minus_SNo_rinv C (omega_SNo C HC).
Qed.

(** ---- Group 3: Markdown Skill Indexing Hygiene ---------------------------- *)

Definition SkillEligible : prop -> prop -> prop :=
  fun is_md is_hidden => is_md /\ ~is_hidden.

Definition skill_index_desc : prop -> prop -> set -> set -> set -> set :=
  fun read_ok valid_desc first_line missing_sentinel read_err =>
    if read_ok then (if valid_desc then first_line else missing_sentinel) else read_err.

Theorem skill_hidden_never_eligible : forall is_md is_hidden:prop, is_hidden -> ~(SkillEligible is_md is_hidden).
let is_md is_hidden. assume Hh Hel.
apply Hel. assume _ Hnh. exact Hnh Hh.
Qed.

Theorem skill_non_md_never_eligible : forall is_md is_hidden:prop, ~is_md -> ~(SkillEligible is_md is_hidden).
let is_md is_hidden. assume Hnmd Hel.
apply Hel. assume Hmd _. exact Hnmd Hmd.
Qed.

Theorem skill_index_valid_preserved : forall read_ok valid_desc:prop, forall line sent err,
  read_ok -> valid_desc -> skill_index_desc read_ok valid_desc line sent err = line.
let read_ok valid_desc. let line sent err. assume Hrok Hvd.
prove (if read_ok then (if valid_desc then line else sent) else err) = line.
rewrite If_i_1 read_ok (if valid_desc then line else sent) err Hrok.
exact If_i_1 valid_desc line sent Hvd.
Qed.

Theorem skill_index_invalid_maps_to_sentinel : forall read_ok valid_desc:prop, forall line sent err,
  read_ok -> ~valid_desc -> skill_index_desc read_ok valid_desc line sent err = sent.
let read_ok valid_desc. let line sent err. assume Hrok Hnvd.
prove (if read_ok then (if valid_desc then line else sent) else err) = sent.
rewrite If_i_1 read_ok (if valid_desc then line else sent) err Hrok.
exact If_i_0 valid_desc line sent Hnvd.
Qed.

Theorem skill_index_unreadable_maps_to_error : forall read_ok valid_desc:prop, forall line sent err,
  ~read_ok -> skill_index_desc read_ok valid_desc line sent err = err.
let read_ok valid_desc. let line sent err. assume Hnrok.
exact If_i_0 read_ok (if valid_desc then line else sent) err Hnrok.
Qed.

(** ---- Group 4: LLM_BACKUP_MODEL Refusal & Error Fallback State Machine ---- *)

Definition FinStop : set := 0.
Definition FinLength : set := 1.
Definition FinToolCalls : set := 2.
Definition FinRefusal : set := 3.
Definition FinContentFilter : set := 4.

Theorem FinToolCalls_neq_Refusal : FinToolCalls <> FinRefusal.
assume Heq : 2 = 3. apply SNoLt_irref 2. rewrite Heq at 2. exact u_nat_In_SNoLt 3 (nat_p_omega 3 nat_3) 2 In_2_3.
Qed.

Theorem FinToolCalls_neq_ContentFilter : FinToolCalls <> FinContentFilter.
assume Heq : 2 = 4. apply SNoLt_irref 2. rewrite Heq at 2. exact u_nat_In_SNoLt 4 (nat_p_omega 4 nat_4) 2 In_2_4.
Qed.

Definition IsRefusal : set -> prop -> prop -> prop -> prop :=
  fun fin ref_fld has_content has_calls =>
    fin = FinRefusal \/ fin = FinContentFilter \/ ref_fld \/ (~has_content /\ ~has_calls).

Theorem refusal_on_refusal_finish : forall ref_fld has_c has_tc:prop,
  IsRefusal FinRefusal ref_fld has_c has_tc.
let ref_fld has_c has_tc.
prove FinRefusal = FinRefusal \/ FinRefusal = FinContentFilter \/ ref_fld \/ (~has_c /\ ~has_tc).
apply orIL. apply orIL. apply orIL. reflexivity.
Qed.

Theorem refusal_on_content_filter : forall ref_fld has_c has_tc:prop,
  IsRefusal FinContentFilter ref_fld has_c has_tc.
let ref_fld has_c has_tc.
prove FinContentFilter = FinRefusal \/ FinContentFilter = FinContentFilter \/ ref_fld \/ (~has_c /\ ~has_tc).
apply orIL. apply orIL. apply orIR. reflexivity.
Qed.

Theorem refusal_on_empty_message : forall fin, forall ref_fld has_c has_tc:prop,
  ~has_c -> ~has_tc -> IsRefusal fin ref_fld has_c has_tc.
let fin. let ref_fld has_c has_tc. assume Hnc Hntc.
prove fin = FinRefusal \/ fin = FinContentFilter \/ ref_fld \/ (~has_c /\ ~has_tc).
apply orIR. exact andI (~has_c) (~has_tc) Hnc Hntc.
Qed.

Theorem non_refusal_on_valid_tool_call : forall ref_fld has_c has_tc:prop,
  ~ref_fld -> has_tc -> ~(IsRefusal FinToolCalls ref_fld has_c has_tc).
let ref_fld has_c has_tc. assume Hnref Htc Href.
apply Href.
- assume H123. apply H123.
  + assume H12. apply H12.
    * assume H : FinToolCalls = FinRefusal. exact FinToolCalls_neq_Refusal H.
    * assume H : FinToolCalls = FinContentFilter. exact FinToolCalls_neq_ContentFilter H.
  + assume Hr : ref_fld. exact Hnref Hr.
- assume Hempty : ~has_c /\ ~has_tc. apply Hempty. assume _ Hntc. exact Hntc Htc.
Qed.

(** Call outcomes and fallback dispatch matching upstream utils.py:393-408 & iter_llm.metta *)
Definition ResOk : set -> set := fun msg => setsum 0 msg.
Definition ResErr : set -> set := fun err => setsum 1 err.

Definition CallOutcome : set -> set -> set -> set :=
  fun used_model res calls => setsum used_model (setsum res calls).
Definition out_model : set -> set := fun r => proj0 r.
Definition out_res : set -> set := fun r => proj0 (proj1 r).
Definition out_calls : set -> set := fun r => proj1 (proj1 r).

Theorem out_model_mk : forall u r n, out_model (CallOutcome u r n) = u.
let u r n. exact proj0_pair_eq u (setsum r n).
Qed.

Theorem out_res_mk : forall u r n, out_res (CallOutcome u r n) = r.
let u r n. prove proj0 (proj1 (setsum u (setsum r n))) = r. rewrite proj1_pair_eq u (setsum r n). exact proj0_pair_eq r n.
Qed.

Theorem out_calls_mk : forall u r n, out_calls (CallOutcome u r n) = n.
let u r n. prove proj1 (proj1 (setsum u (setsum r n))) = n. rewrite proj1_pair_eq u (setsum r n). exact proj1_pair_eq r n.
Qed.

Definition UseBackup : set -> set -> prop := fun model backup => backup <> 0 /\ backup <> model.

(** Exact dispatch function over primary status (primary_ok, primary_refused, primary_res)
    and backup status (backup_ok, backup_res). 0 represents unset LLM_BACKUP_MODEL = "". *)
Definition backup_dispatch : set -> set -> prop -> prop -> set -> prop -> set -> set :=
  fun model backup p_ok p_ref p_res b_ok b_res =>
    if p_ok then
      (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
    else
      (if UseBackup model backup then
         (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2)
       else
         CallOutcome model p_res 1).

Theorem fallback_disabled_when_unset :
  forall model, forall p_ok p_ref:prop, forall p_res, forall b_ok:prop, forall b_res,
  backup_dispatch model 0 p_ok p_ref p_res b_ok b_res = CallOutcome model p_res 1.
let model. let p_ok p_ref. let p_res. let b_ok. let b_res.
claim Hnu : ~(UseBackup model 0).
{ assume Hu : 0 <> 0 /\ 0 <> model. apply Hu. assume H0 _. apply H0. reflexivity. }
claim Hnur : ~(UseBackup model 0 /\ p_ref).
{ assume H. apply H. assume Hu _. exact Hnu Hu. }
apply xm p_ok.
- assume Hok : p_ok.
  prove (if p_ok then (if UseBackup model 0 /\ p_ref then CallOutcome 0 b_res 2 else CallOutcome model p_res 1)
         else (if UseBackup model 0 then (if b_ok then CallOutcome 0 b_res 2 else CallOutcome model p_res 2)
               else CallOutcome model p_res 1)) = CallOutcome model p_res 1.
  rewrite If_i_1 p_ok (if UseBackup model 0 /\ p_ref then CallOutcome 0 b_res 2 else CallOutcome model p_res 1)
          (if UseBackup model 0 then (if b_ok then CallOutcome 0 b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hok.
  exact If_i_0 (UseBackup model 0 /\ p_ref) (CallOutcome 0 b_res 2) (CallOutcome model p_res 1) Hnur.
- assume Hnok : ~p_ok.
  prove (if p_ok then (if UseBackup model 0 /\ p_ref then CallOutcome 0 b_res 2 else CallOutcome model p_res 1)
         else (if UseBackup model 0 then (if b_ok then CallOutcome 0 b_res 2 else CallOutcome model p_res 2)
               else CallOutcome model p_res 1)) = CallOutcome model p_res 1.
  rewrite If_i_0 p_ok (if UseBackup model 0 /\ p_ref then CallOutcome 0 b_res 2 else CallOutcome model p_res 1)
          (if UseBackup model 0 then (if b_ok then CallOutcome 0 b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hnok.
  exact If_i_0 (UseBackup model 0) (if b_ok then CallOutcome 0 b_res 2 else CallOutcome model p_res 2) (CallOutcome model p_res 1) Hnu.
Qed.

Theorem fallback_disabled_when_same_model :
  forall model, forall p_ok p_ref:prop, forall p_res, forall b_ok:prop, forall b_res,
  backup_dispatch model model p_ok p_ref p_res b_ok b_res = CallOutcome model p_res 1.
let model. let p_ok p_ref. let p_res. let b_ok. let b_res.
claim Hnu : ~(UseBackup model model).
{ assume Hu : model <> 0 /\ model <> model. apply Hu. assume _ Hm. apply Hm. reflexivity. }
claim Hnur : ~(UseBackup model model /\ p_ref).
{ assume H. apply H. assume Hu _. exact Hnu Hu. }
apply xm p_ok.
- assume Hok : p_ok.
  prove (if p_ok then (if UseBackup model model /\ p_ref then CallOutcome model b_res 2 else CallOutcome model p_res 1)
         else (if UseBackup model model then (if b_ok then CallOutcome model b_res 2 else CallOutcome model p_res 2)
               else CallOutcome model p_res 1)) = CallOutcome model p_res 1.
  rewrite If_i_1 p_ok (if UseBackup model model /\ p_ref then CallOutcome model b_res 2 else CallOutcome model p_res 1)
          (if UseBackup model model then (if b_ok then CallOutcome model b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hok.
  exact If_i_0 (UseBackup model model /\ p_ref) (CallOutcome model b_res 2) (CallOutcome model p_res 1) Hnur.
- assume Hnok : ~p_ok.
  prove (if p_ok then (if UseBackup model model /\ p_ref then CallOutcome model b_res 2 else CallOutcome model p_res 1)
         else (if UseBackup model model then (if b_ok then CallOutcome model b_res 2 else CallOutcome model p_res 2)
               else CallOutcome model p_res 1)) = CallOutcome model p_res 1.
  rewrite If_i_0 p_ok (if UseBackup model model /\ p_ref then CallOutcome model b_res 2 else CallOutcome model p_res 1)
          (if UseBackup model model then (if b_ok then CallOutcome model b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hnok.
  exact If_i_0 (UseBackup model model) (if b_ok then CallOutcome model b_res 2 else CallOutcome model p_res 2) (CallOutcome model p_res 1) Hnu.
Qed.

Theorem fallback_valid_primary_never_calls_backup :
  forall model backup, forall p_ok p_ref:prop, forall p_res, forall b_ok:prop, forall b_res,
  p_ok -> ~p_ref ->
  backup_dispatch model backup p_ok p_ref p_res b_ok b_res = CallOutcome model p_res 1.
let model backup. let p_ok p_ref. let p_res. let b_ok. let b_res. assume Hok Hnref.
claim Hnur : ~(UseBackup model backup /\ p_ref).
{ assume H. apply H. assume _ Hr. exact Hnref Hr. }
prove (if p_ok then (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
       else (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2)
             else CallOutcome model p_res 1)) = CallOutcome model p_res 1.
rewrite If_i_1 p_ok (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
        (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hok.
exact If_i_0 (UseBackup model backup /\ p_ref) (CallOutcome backup b_res 2) (CallOutcome model p_res 1) Hnur.
Qed.

Theorem fallback_refusal_switches_to_backup :
  forall model backup, UseBackup model backup ->
  forall p_ok p_ref:prop, forall p_res, forall b_ok:prop, forall b_res,
  p_ok -> p_ref ->
  backup_dispatch model backup p_ok p_ref p_res b_ok b_res = CallOutcome backup b_res 2.
let model backup. assume Hub. let p_ok p_ref. let p_res. let b_ok. let b_res. assume Hok Href.
prove (if p_ok then (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
       else (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2)
             else CallOutcome model p_res 1)) = CallOutcome backup b_res 2.
rewrite If_i_1 p_ok (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
        (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hok.
exact If_i_1 (UseBackup model backup /\ p_ref) (CallOutcome backup b_res 2) (CallOutcome model p_res 1) (andI (UseBackup model backup) p_ref Hub Href).
Qed.

Theorem fallback_primary_error_recovers_on_backup :
  forall model backup, UseBackup model backup ->
  forall p_ok p_ref:prop, forall p_res, forall b_ok:prop, forall b_res,
  ~p_ok -> b_ok ->
  backup_dispatch model backup p_ok p_ref p_res b_ok b_res = CallOutcome backup b_res 2.
let model backup. assume Hub. let p_ok p_ref. let p_res. let b_ok. let b_res. assume Hnok Hbok.
prove (if p_ok then (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
       else (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2)
             else CallOutcome model p_res 1)) = CallOutcome backup b_res 2.
rewrite If_i_0 p_ok (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
        (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hnok.
rewrite If_i_1 (UseBackup model backup) (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) (CallOutcome model p_res 1) Hub.
exact If_i_1 b_ok (CallOutcome backup b_res 2) (CallOutcome model p_res 2) Hbok.
Qed.

Theorem fallback_double_error_preserves_primary_error :
  forall model backup, UseBackup model backup ->
  forall p_ok p_ref:prop, forall e1, forall b_ok:prop, forall e2,
  ~p_ok -> ~b_ok ->
  out_res (backup_dispatch model backup p_ok p_ref (ResErr e1) b_ok (ResErr e2)) = ResErr e1 /\
  out_calls (backup_dispatch model backup p_ok p_ref (ResErr e1) b_ok (ResErr e2)) = 2.
let model backup. assume Hub. let p_ok p_ref. let e1. let b_ok. let e2. assume Hnok Hnbok.
claim Heq : backup_dispatch model backup p_ok p_ref (ResErr e1) b_ok (ResErr e2) = CallOutcome model (ResErr e1) 2.
{ prove (if p_ok then (if UseBackup model backup /\ p_ref then CallOutcome backup (ResErr e2) 2 else CallOutcome model (ResErr e1) 1)
         else (if UseBackup model backup then (if b_ok then CallOutcome backup (ResErr e2) 2 else CallOutcome model (ResErr e1) 2)
               else CallOutcome model (ResErr e1) 1)) = CallOutcome model (ResErr e1) 2.
  rewrite If_i_0 p_ok (if UseBackup model backup /\ p_ref then CallOutcome backup (ResErr e2) 2 else CallOutcome model (ResErr e1) 1)
          (if UseBackup model backup then (if b_ok then CallOutcome backup (ResErr e2) 2 else CallOutcome model (ResErr e1) 2) else CallOutcome model (ResErr e1) 1) Hnok.
  rewrite If_i_1 (UseBackup model backup) (if b_ok then CallOutcome backup (ResErr e2) 2 else CallOutcome model (ResErr e1) 2) (CallOutcome model (ResErr e1) 1) Hub.
  exact If_i_0 b_ok (CallOutcome backup (ResErr e2) 2) (CallOutcome model (ResErr e1) 2) Hnbok. }
rewrite Heq.
apply andI.
- exact out_res_mk model (ResErr e1) 2.
- exact out_calls_mk model (ResErr e1) 2.
Qed.

Theorem fallback_calls_bounded_1_to_2 :
  forall model backup, forall p_ok p_ref:prop, forall p_res, forall b_ok:prop, forall b_res,
  1 <= out_calls (backup_dispatch model backup p_ok p_ref p_res b_ok b_res) /\
  out_calls (backup_dispatch model backup p_ok p_ref p_res b_ok b_res) <= 2.
let model backup. let p_ok p_ref. let p_res. let b_ok. let b_res.
claim H1le2 : 1 <= 2. { exact SNoLtLe 1 2 (u_nat_In_SNoLt 2 u_nat_2_omega 1 In_1_2). }
apply xm p_ok.
- assume Hok : p_ok.
  apply xm (UseBackup model backup /\ p_ref).
  + assume Hbr : UseBackup model backup /\ p_ref.
    claim Heq : backup_dispatch model backup p_ok p_ref p_res b_ok b_res = CallOutcome backup b_res 2.
    { apply Hbr. assume Hub Href. exact fallback_refusal_switches_to_backup model backup Hub p_ok p_ref p_res b_ok b_res Hok Href. }
    rewrite Heq. rewrite out_calls_mk backup b_res 2.
    exact andI (1 <= 2) (2 <= 2) H1le2 (SNoLe_ref 2).
  + assume Hnbr : ~(UseBackup model backup /\ p_ref).
    claim Heq : backup_dispatch model backup p_ok p_ref p_res b_ok b_res = CallOutcome model p_res 1.
    { prove (if p_ok then (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
             else (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1)) = CallOutcome model p_res 1.
      rewrite If_i_1 p_ok (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
              (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hok.
      exact If_i_0 (UseBackup model backup /\ p_ref) (CallOutcome backup b_res 2) (CallOutcome model p_res 1) Hnbr. }
    rewrite Heq. rewrite out_calls_mk model p_res 1.
    exact andI (1 <= 1) (1 <= 2) (SNoLe_ref 1) H1le2.
- assume Hnok : ~p_ok.
  apply xm (UseBackup model backup).
  + assume Hub : UseBackup model backup.
    apply xm b_ok.
    * assume Hbok : b_ok.
      rewrite fallback_primary_error_recovers_on_backup model backup Hub p_ok p_ref p_res b_ok b_res Hnok Hbok.
      rewrite out_calls_mk backup b_res 2.
      exact andI (1 <= 2) (2 <= 2) H1le2 (SNoLe_ref 2).
    * assume Hnbok : ~b_ok.
      claim Heq : backup_dispatch model backup p_ok p_ref p_res b_ok b_res = CallOutcome model p_res 2.
      { prove (if p_ok then (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
               else (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1)) = CallOutcome model p_res 2.
        rewrite If_i_0 p_ok (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
                (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hnok.
        rewrite If_i_1 (UseBackup model backup) (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) (CallOutcome model p_res 1) Hub.
        exact If_i_0 b_ok (CallOutcome backup b_res 2) (CallOutcome model p_res 2) Hnbok. }
      rewrite Heq. rewrite out_calls_mk model p_res 2.
      exact andI (1 <= 2) (2 <= 2) H1le2 (SNoLe_ref 2).
  + assume Hnub : ~(UseBackup model backup).
    claim Heq : backup_dispatch model backup p_ok p_ref p_res b_ok b_res = CallOutcome model p_res 1.
    { prove (if p_ok then (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
             else (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1)) = CallOutcome model p_res 1.
      rewrite If_i_0 p_ok (if UseBackup model backup /\ p_ref then CallOutcome backup b_res 2 else CallOutcome model p_res 1)
              (if UseBackup model backup then (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) else CallOutcome model p_res 1) Hnok.
      exact If_i_0 (UseBackup model backup) (if b_ok then CallOutcome backup b_res 2 else CallOutcome model p_res 2) (CallOutcome model p_res 1) Hnub. }
    rewrite Heq. rewrite out_calls_mk model p_res 1.
    exact andI (1 <= 1) (1 <= 2) (SNoLe_ref 1) H1le2.
Qed.

End IterUpstreamExtensions.
