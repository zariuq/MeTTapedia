(** ========================================================================== *)
(** Iter Formal Verification in Megalodon (Egal)                               *)
(** Module 01: NAL Truth-Value & Tool-Reliability Algebra                      *)
(** Faithful to iter/lib_nal.metta and iter/lib_reliability.metta              *)
(** Zero document axioms — built strictly on the standard Egal preamble.       *)
(** ========================================================================== *)

Section IterNALTruth.

Prefix - 358 := minus_SNo.
Infix + 360 right := add_SNo.
Infix * 355 right := mul_SNo.
Infix :/: 353 := div_SNo.

(** ---- Core real-field division & order lemmas ----------------------------- *)

Theorem real_sub : forall x y :e real, x + - y :e real.
let x. assume Hx. let y. assume Hy.
apply real_add_SNo.
- exact Hx.
- exact real_minus_SNo y Hy.
Qed.

Theorem SNo_mul_cancel_R : forall x y z, SNo x -> SNo y -> SNo z -> z <> 0 -> x * z = y * z -> x = y.
let x y z. assume Hx Hy Hz Hz0 Heq.
claim Hdiff : (x + - y) * z = 0.
{ rewrite mul_SNo_distrR x (- y) z Hx (SNo_minus_SNo y Hy) Hz.
  rewrite mul_SNo_minus_distrL y z Hy Hz.
  rewrite Heq.
  exact add_SNo_minus_SNo_rinv (y * z) (SNo_mul_SNo y z Hy Hz). }
claim Hxy0 : x + - y = 0.
{ apply dneg. assume Hne : x + - y <> 0.
  exact mul_SNo_nonzero (x + - y) z (SNo_add_SNo x (- y) Hx (SNo_minus_SNo y Hy)) Hz Hne Hz0 Hdiff. }
rewrite <- add_SNo_minus_R2' x y Hx Hy.
rewrite Hxy0.
exact add_SNo_0L y Hy.
Qed.

Theorem real_div_spec : forall x y :e real, y <> 0 -> (x :/: y) :e real /\ (x :/: y) * y = x.
let x. assume Hx. let y. assume Hy Hy0.
claim Hinv : exists w :e real, y * w = 1.
{ exact nonzero_real_recip_ex y Hy Hy0. }
apply Hinv. let w. assume Hw. apply Hw. assume Hwr Hyw.
claim Hxw : (x * w) * y = x.
{ rewrite <- mul_SNo_assoc x w y (real_SNo x Hx) (real_SNo w Hwr) (real_SNo y Hy).
  rewrite mul_SNo_com w y (real_SNo w Hwr) (real_SNo y Hy).
  rewrite Hyw.
  exact mul_SNo_oneR x (real_SNo x Hx). }
claim Hdiv_def : x :/: y = Eps_i (fun z => SNo z /\ z * y = x).
{ exact If_i_0 (y = 0) 0 (Eps_i (fun z => SNo z /\ z * y = x)) Hy0. }
claim Hex : SNo (x * w) /\ (x * w) * y = x.
{ apply andI.
  - exact SNo_mul_SNo x w (real_SNo x Hx) (real_SNo w Hwr).
  - exact Hxw. }
claim Heps : SNo (Eps_i (fun z => SNo z /\ z * y = x)) /\ Eps_i (fun z => SNo z /\ z * y = x) * y = x.
{ exact Eps_i_ax (fun z => SNo z /\ z * y = x) (x * w) Hex. }
claim Heq : x :/: y = x * w.
{ rewrite Hdiv_def.
  apply SNo_mul_cancel_R (Eps_i (fun z => SNo z /\ z * y = x)) (x * w) y
        (andEL (SNo (Eps_i (fun z => SNo z /\ z * y = x))) (Eps_i (fun z => SNo z /\ z * y = x) * y = x) Heps)
        (SNo_mul_SNo x w (real_SNo x Hx) (real_SNo w Hwr))
        (real_SNo y Hy) Hy0.
  rewrite (andER (SNo (Eps_i (fun z => SNo z /\ z * y = x))) (Eps_i (fun z => SNo z /\ z * y = x) * y = x) Heps).
  symmetry. exact Hxw. }
rewrite Heq.
apply andI.
- exact real_mul_SNo x Hx w Hwr.
- exact Hxw.
Qed.

Theorem real_div_real : forall x y :e real, y <> 0 -> (x :/: y) :e real.
let x. assume Hx. let y. assume Hy Hy0.
exact andEL ((x :/: y) :e real) ((x :/: y) * y = x) (real_div_spec x Hx y Hy Hy0).
Qed.

Theorem real_div_mul_cancel : forall x y :e real, y <> 0 -> (x :/: y) * y = x.
let x. assume Hx. let y. assume Hy Hy0.
exact andER ((x :/: y) :e real) ((x :/: y) * y = x) (real_div_spec x Hx y Hy Hy0).
Qed.

Theorem real_pos_neq0 : forall x, SNo x -> 0 < x -> x <> 0.
let x. assume Hx Hpos Heq.
apply SNoLt_irref 0.
rewrite <- Heq at 2.
exact Hpos.
Qed.

Theorem SNo_mul_Lt_pos_R : forall a b c, SNo a -> SNo b -> SNo c -> 0 < c -> a < b -> a * c < b * c.
let a b c. assume Ha Hb Hc Hc0 Hab.
claim Hba : 0 < b + - a.
{ rewrite <- add_SNo_minus_SNo_rinv a Ha.
  exact add_SNo_Lt1 a (- a) b Ha (SNo_minus_SNo a Ha) Hb Hab. }
claim Hprod : 0 < (b + - a) * c.
{ exact mul_SNo_pos_pos (b + - a) c (SNo_add_SNo b (- a) Hb (SNo_minus_SNo a Ha)) Hc Hba Hc0. }
claim Hdist : (b + - a) * c = b * c + - (a * c).
{ rewrite mul_SNo_distrR b (- a) c Hb (SNo_minus_SNo a Ha) Hc.
  rewrite mul_SNo_minus_distrL a c Ha Hc.
  reflexivity. }
claim Hpos : 0 < b * c + - (a * c).
{ rewrite <- Hdist. exact Hprod. }
claim Hstep : 0 + a * c < b * c.
{ exact add_SNo_minus_Lt2 (b * c) (a * c) 0 (SNo_mul_SNo b c Hb Hc) (SNo_mul_SNo a c Ha Hc) SNo_0 Hpos. }
rewrite <- add_SNo_0L (a * c) (SNo_mul_SNo a c Ha Hc).
exact Hstep.
Qed.

Theorem SNo_mul_Le_pos_R : forall a b c, SNo a -> SNo b -> SNo c -> 0 <= c -> a <= b -> a * c <= b * c.
let a b c. assume Ha Hb Hc Hc0 Hab.
apply SNoLeE 0 c SNo_0 Hc Hc0.
- assume Hcp : 0 < c.
  apply SNoLeE a b Ha Hb Hab.
  + assume Hlt : a < b.
    exact SNoLtLe (a * c) (b * c) (SNo_mul_Lt_pos_R a b c Ha Hb Hc Hcp Hlt).
  + assume Heq : a = b.
    rewrite Heq. exact SNoLe_ref (b * c).
- assume Hc_eq : 0 = c.
  rewrite <- Hc_eq.
  rewrite mul_SNo_zeroR a Ha.
  rewrite mul_SNo_zeroR b Hb.
  exact SNoLe_ref 0.
Qed.

Theorem SNo_mul_Lt_pos_cancel_R : forall a b c, SNo a -> SNo b -> SNo c -> 0 < c -> a * c < b * c -> a < b.
let a b c. assume Ha Hb Hc Hc0 Hlt.
apply SNoLtLe_or a b Ha Hb.
- assume H : a < b. exact H.
- assume Hba : b <= a.
  claim Hle : b * c <= a * c.
  { exact SNo_mul_Le_pos_R b a c Hb Ha Hc (SNoLtLe 0 c Hc0) Hba. }
  apply FalseE.
  exact SNoLt_irref (a * c) (SNoLtLe_tra (a * c) (b * c) (a * c)
        (SNo_mul_SNo a c Ha Hc) (SNo_mul_SNo b c Hb Hc) (SNo_mul_SNo a c Ha Hc) Hlt Hle).
Qed.

Theorem SNo_mul_Le_pos_cancel_R : forall a b c, SNo a -> SNo b -> SNo c -> 0 < c -> a * c <= b * c -> a <= b.
let a b c. assume Ha Hb Hc Hc0 Hle.
apply SNoLtLe_or b a Hb Ha.
- assume Hba : b < a.
  claim Hlt : b * c < a * c.
  { exact SNo_mul_Lt_pos_R b a c Hb Ha Hc Hc0 Hba. }
  apply FalseE.
  exact SNoLt_irref (b * c) (SNoLtLe_tra (b * c) (a * c) (b * c)
        (SNo_mul_SNo b c Hb Hc) (SNo_mul_SNo a c Ha Hc) (SNo_mul_SNo b c Hb Hc) Hlt Hle).
- assume Hab : a <= b. exact Hab.
Qed.

Theorem real_div_nonneg : forall x y :e real, 0 <= x -> 0 < y -> 0 <= x :/: y.
let x. assume Hx. let y. assume Hy Hx0 Hy0.
claim Hyne : y <> 0. { exact real_pos_neq0 y (real_SNo y Hy) Hy0. }
claim Hq : (x :/: y) :e real. { exact real_div_real x Hx y Hy Hyne. }
apply SNo_mul_Le_pos_cancel_R 0 (x :/: y) y SNo_0 (real_SNo (x :/: y) Hq) (real_SNo y Hy) Hy0.
rewrite mul_SNo_zeroL y (real_SNo y Hy).
rewrite real_div_mul_cancel x Hx y Hy Hyne.
exact Hx0.
Qed.

Theorem real_div_pos : forall x y :e real, 0 < x -> 0 < y -> 0 < x :/: y.
let x. assume Hx. let y. assume Hy Hx0 Hy0.
claim Hyne : y <> 0. { exact real_pos_neq0 y (real_SNo y Hy) Hy0. }
claim Hq : (x :/: y) :e real. { exact real_div_real x Hx y Hy Hyne. }
apply SNo_mul_Lt_pos_cancel_R 0 (x :/: y) y SNo_0 (real_SNo (x :/: y) Hq) (real_SNo y Hy) Hy0.
rewrite mul_SNo_zeroL y (real_SNo y Hy).
rewrite real_div_mul_cancel x Hx y Hy Hyne.
exact Hx0.
Qed.

Theorem real_div_lt_1 : forall x y :e real, 0 < y -> x < y -> (x :/: y) < 1.
let x. assume Hx. let y. assume Hy Hy0 Hxy.
claim Hyne : y <> 0. { exact real_pos_neq0 y (real_SNo y Hy) Hy0. }
claim Hq : (x :/: y) :e real. { exact real_div_real x Hx y Hy Hyne. }
apply SNo_mul_Lt_pos_cancel_R (x :/: y) 1 y (real_SNo (x :/: y) Hq) SNo_1 (real_SNo y Hy) Hy0.
rewrite real_div_mul_cancel x Hx y Hy Hyne.
rewrite mul_SNo_oneL y (real_SNo y Hy).
exact Hxy.
Qed.

Theorem real_div_le_1 : forall x y :e real, 0 < y -> x <= y -> (x :/: y) <= 1.
let x. assume Hx. let y. assume Hy Hy0 Hxy.
claim Hyne : y <> 0. { exact real_pos_neq0 y (real_SNo y Hy) Hy0. }
claim Hq : (x :/: y) :e real. { exact real_div_real x Hx y Hy Hyne. }
apply SNo_mul_Le_pos_cancel_R (x :/: y) 1 y (real_SNo (x :/: y) Hq) SNo_1 (real_SNo y Hy) Hy0.
rewrite real_div_mul_cancel x Hx y Hy Hyne.
rewrite mul_SNo_oneL y (real_SNo y Hy).
exact Hxy.
Qed.

Theorem real_unit_prod_le_1 : forall x y :e real, 0 <= x -> x <= 1 -> 0 <= y -> y <= 1 -> x * y <= 1.
let x. assume Hx. let y. assume Hy Hx0 Hx1 Hy0 Hy1.
claim H1 : x * y <= y.
{ rewrite <- mul_SNo_oneL y (real_SNo y Hy) at 2.
  exact SNo_mul_Le_pos_R x 1 y (real_SNo x Hx) SNo_1 (real_SNo y Hy) Hy0 Hx1. }
exact SNoLe_tra (x * y) y 1 (SNo_mul_SNo x y (real_SNo x Hx) (real_SNo y Hy)) (real_SNo y Hy) SNo_1 H1 Hy1.
Qed.

Theorem real_unit_prod_nonneg : forall x y :e real, 0 <= x -> 0 <= y -> 0 <= x * y.
let x. assume Hx. let y. assume Hy Hx0 Hy0.
rewrite <- mul_SNo_zeroL y (real_SNo y Hy).
exact SNo_mul_Le_pos_R 0 x y SNo_0 (real_SNo x Hx) (real_SNo y Hy) Hy0 Hx0.
Qed.

Theorem real_unit_prod_lt_1 : forall x y :e real, 0 <= x -> x <= 1 -> 0 <= y -> y < 1 -> x * y < 1.
let x. assume Hx. let y. assume Hy Hx0 Hx1 Hy0 Hy1.
claim H1 : x * y <= y.
{ rewrite <- mul_SNo_oneL y (real_SNo y Hy) at 2.
  exact SNo_mul_Le_pos_R x 1 y (real_SNo x Hx) SNo_1 (real_SNo y Hy) Hy0 Hx1. }
exact SNoLeLt_tra (x * y) y 1 (SNo_mul_SNo x y (real_SNo x Hx) (real_SNo y Hy)) (real_SNo y Hy) SNo_1 H1 Hy1.
Qed.

Theorem real_one_minus_pos : forall c :e real, c < 1 -> 0 < 1 + - c.
let c. assume Hc Hc1.
rewrite <- add_SNo_minus_SNo_rinv c (real_SNo c Hc) at 1.
exact add_SNo_Lt1 c (- c) 1 (real_SNo c Hc) (SNo_minus_SNo c (real_SNo c Hc)) SNo_1 Hc1.
Qed.

Theorem real_one_minus_nonneg : forall x :e real, x <= 1 -> 0 <= 1 + - x.
let x. assume Hx Hx1.
rewrite <- add_SNo_minus_SNo_rinv x (real_SNo x Hx) at 1.
exact add_SNo_Le1 x (- x) 1 (real_SNo x Hx) (SNo_minus_SNo x (real_SNo x Hx)) SNo_1 Hx1.
Qed.

Theorem real_one_minus_le_1 : forall x :e real, 0 <= x -> 1 + - x <= 1.
let x. assume Hx Hx0.
claim Hmx : - x <= 0.
{ rewrite <- minus_SNo_0.
  exact minus_SNo_Le_contra 0 x SNo_0 (real_SNo x Hx) Hx0. }
rewrite <- add_SNo_0R 1 SNo_1 at 2.
exact add_SNo_Le2 1 (- x) 0 SNo_1 (SNo_minus_SNo x (real_SNo x Hx)) SNo_0 Hmx.
Qed.

(** ---- Iter NAL Truth-Value Definitions (lib_nal.metta) -------------------- *)

Definition ValidFreq : set -> prop := fun f => f :e real /\ 0 <= f /\ f <= 1.
Definition ValidConf : set -> prop := fun c => c :e real /\ 0 <= c /\ c < 1.
Definition ValidWeight : set -> prop := fun w => w :e real /\ 0 <= w.

Definition STV : set -> set -> set := fun f c => setsum f c.
Definition stv_f : set -> set := proj0.
Definition stv_c : set -> set := proj1.

Definition ValidSTV : set -> prop := fun tv => ValidFreq (stv_f tv) /\ ValidConf (stv_c tv).

Theorem ValidFreqI : forall f, f :e real -> 0 <= f -> f <= 1 -> ValidFreq f.
let f. assume Hr H0 H1.
prove f :e real /\ 0 <= f /\ f <= 1.
exact andI (f :e real /\ 0 <= f) (f <= 1) (andI (f :e real) (0 <= f) Hr H0) H1.
Qed.

Theorem ValidConfI : forall c, c :e real -> 0 <= c -> c < 1 -> ValidConf c.
let c. assume Hr H0 H1.
prove c :e real /\ 0 <= c /\ c < 1.
exact andI (c :e real /\ 0 <= c) (c < 1) (andI (c :e real) (0 <= c) Hr H0) H1.
Qed.

Theorem ValidWeightI : forall w, w :e real -> 0 <= w -> ValidWeight w.
let w. assume Hr H0.
prove w :e real /\ 0 <= w.
exact andI (w :e real) (0 <= w) Hr H0.
Qed.

Theorem ValidSTVI : forall tv, ValidFreq (stv_f tv) -> ValidConf (stv_c tv) -> ValidSTV tv.
let tv. assume Hf Hc.
prove ValidFreq (stv_f tv) /\ ValidConf (stv_c tv).
exact andI (ValidFreq (stv_f tv)) (ValidConf (stv_c tv)) Hf Hc.
Qed.

Definition Truth_c2w : set -> set := fun c => c :/: (1 + - c).
Definition Truth_w2c : set -> set := fun w => w :/: (w + 1).

Definition Truth_or : set -> set -> set := fun a b => 1 + - ((1 + - a) * (1 + - b)).

Definition Truth_Negation : set -> set := fun tv => STV (1 + - stv_f tv) (stv_c tv).
Definition Truth_Deduction : set -> set -> set :=
  fun t1 t2 => STV (stv_f t1 * stv_f t2) ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)).
Definition Truth_Intersection : set -> set -> set :=
  fun t1 t2 => STV (stv_f t1 * stv_f t2) (stv_c t1 * stv_c t2).
Definition Truth_Abduction : set -> set -> set :=
  fun t1 t2 => STV (stv_f t2) (Truth_w2c ((stv_f t1 * stv_c t1) * stv_c t2)).
Definition Truth_Induction : set -> set -> set :=
  fun t1 t2 => Truth_Abduction t2 t1.
Definition Truth_Exemplification : set -> set -> set :=
  fun t1 t2 => STV 1 (Truth_w2c ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2))).
Definition Truth_Analogy : set -> set -> set :=
  fun t1 t2 => STV (stv_f t1 * stv_f t2) ((stv_c t1 * stv_c t2) * stv_f t2).
Definition Truth_Union : set -> set -> set :=
  fun t1 t2 => STV (Truth_or (stv_f t1) (stv_f t2)) (stv_c t1 * stv_c t2).
Definition Truth_Difference : set -> set -> set :=
  fun t1 t2 => STV (stv_f t1 * (1 + - stv_f t2)) (stv_c t1 * stv_c t2).
Definition Truth_Eternalize : set -> set :=
  fun tv => STV (stv_f tv) (Truth_w2c (stv_c tv)).

(** Core unclipped revision formula from lib_nal.metta:92-99 *)
Definition Truth_Rev_w : set -> set -> set := fun c1 c2 => Truth_c2w c1 + Truth_c2w c2.
Definition Truth_Rev_f : set -> set -> set -> set -> set :=
  fun f1 c1 f2 c2 => (Truth_c2w c1 * f1 + Truth_c2w c2 * f2) :/: Truth_Rev_w c1 c2.
Definition Truth_Rev_c : set -> set -> set :=
  fun c1 c2 => Truth_w2c (Truth_Rev_w c1 c2).

(** Tool reliability single-observation update from lib_reliability.metta:63-67 *)
Definition Rel_Revise_f : set -> set -> set -> set :=
  fun f c obs => (Truth_c2w c * f + obs) :/: (Truth_c2w c + 1).
Definition Rel_Revise_c : set -> set :=
  fun c => Truth_w2c (Truth_c2w c + 1).

(** Truth expectation from lib_nal.metta:11 *)
Definition half : set := 1 :/: (1 + 1).
Definition Truth_Expectation : set -> set -> set :=
  fun f c => c * (f + - half) + half.

(** ---- Unfolding Cancellation Lemmas --------------------------------------- *)

Theorem Truth_c2w_mul : forall c, ValidConf c -> Truth_c2w c * (1 + - c) = c.
let c. assume Hc.
apply Hc. assume Hcr0 Hc1. apply Hcr0. assume Hcr Hc0.
claim Hden_r : (1 + - c) :e real. { exact real_sub 1 real_1 c Hcr. }
claim Hden_ne : 1 + - c <> 0.
{ exact real_pos_neq0 (1 + - c) (real_SNo (1 + - c) Hden_r) (real_one_minus_pos c Hcr Hc1). }
prove (c :/: (1 + - c)) * (1 + - c) = c.
exact real_div_mul_cancel c Hcr (1 + - c) Hden_r Hden_ne.
Qed.

Theorem Truth_w2c_mul : forall w, ValidWeight w -> Truth_w2c w * (w + 1) = w.
let w. assume Hw. apply Hw. assume Hwr Hw0.
claim Hw1_r : (w + 1) :e real. { exact real_add_SNo w Hwr 1 real_1. }
claim Hw1_p : 0 < w + 1.
{ apply SNoLeLt_tra 0 w (w + 1) SNo_0 (real_SNo w Hwr) (real_SNo (w + 1) Hw1_r) Hw0.
  rewrite <- add_SNo_0R w (real_SNo w Hwr) at 1.
  exact add_SNo_Lt2 w 0 1 (real_SNo w Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hw1_ne : w + 1 <> 0. { exact real_pos_neq0 (w + 1) (real_SNo (w + 1) Hw1_r) Hw1_p. }
prove (w :/: (w + 1)) * (w + 1) = w.
exact real_div_mul_cancel w Hwr (w + 1) Hw1_r Hw1_ne.
Qed.

(** ---- Theorem Group 1: c2w <-> w2c Order-Preserving Bijection ------------- *)

Theorem Truth_c2w_valid : forall c, ValidConf c -> ValidWeight (Truth_c2w c).
let c. assume Hc.
apply Hc. assume Hc_rc Hc1. apply Hc_rc. assume Hcr Hc0.
claim Hden_r : (1 + - c) :e real. { exact real_sub 1 real_1 c Hcr. }
claim Hden_p : 0 < 1 + - c. { exact real_one_minus_pos c Hcr Hc1. }
claim Hden_ne : 1 + - c <> 0. { exact real_pos_neq0 (1 + - c) (real_SNo (1 + - c) Hden_r) Hden_p. }
apply ValidWeightI.
- exact real_div_real c Hcr (1 + - c) Hden_r Hden_ne.
- exact real_div_nonneg c Hcr (1 + - c) Hden_r Hc0 Hden_p.
Qed.

Theorem Truth_w2c_valid : forall w, ValidWeight w -> ValidConf (Truth_w2c w).
let w. assume Hw. apply Hw. assume Hwr Hw0.
claim Hw1_r : (w + 1) :e real. { exact real_add_SNo w Hwr 1 real_1. }
claim Hw1_p : 0 < w + 1.
{ apply SNoLeLt_tra 0 w (w + 1) SNo_0 (real_SNo w Hwr) (real_SNo (w + 1) Hw1_r) Hw0.
  rewrite <- add_SNo_0R w (real_SNo w Hwr) at 1.
  exact add_SNo_Lt2 w 0 1 (real_SNo w Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hw1_ne : w + 1 <> 0. { exact real_pos_neq0 (w + 1) (real_SNo (w + 1) Hw1_r) Hw1_p. }
claim Hw_lt : w < w + 1.
{ rewrite <- add_SNo_0R w (real_SNo w Hwr) at 1.
  exact add_SNo_Lt2 w 0 1 (real_SNo w Hwr) SNo_0 SNo_1 SNoLt_0_1. }
apply ValidConfI.
- exact real_div_real w Hwr (w + 1) Hw1_r Hw1_ne.
- exact real_div_nonneg w Hwr (w + 1) Hw1_r Hw0 Hw1_p.
- exact real_div_lt_1 w Hwr (w + 1) Hw1_r Hw1_p Hw_lt.
Qed.

Theorem Truth_w2c_c2w_inv : forall c, ValidConf c -> Truth_w2c (Truth_c2w c) = c.
let c. assume Hc.
apply Hc. assume Hc_rc Hc1. apply Hc_rc. assume Hcr Hc0.
claim Hden_r : (1 + - c) :e real. { exact real_sub 1 real_1 c Hcr. }
claim Hden_p : 0 < 1 + - c. { exact real_one_minus_pos c Hcr Hc1. }
claim Hden_ne : 1 + - c <> 0. { exact real_pos_neq0 (1 + - c) (real_SNo (1 + - c) Hden_r) Hden_p. }
claim Hw : ValidWeight (Truth_c2w c). { exact Truth_c2w_valid c Hc. }
claim Hwr : Truth_c2w c :e real. { exact andEL (Truth_c2w c :e real) (0 <= Truth_c2w c) Hw. }
claim Hw0 : 0 <= Truth_c2w c. { exact andER (Truth_c2w c :e real) (0 <= Truth_c2w c) Hw. }
claim Hw1_r : (Truth_c2w c + 1) :e real. { exact real_add_SNo (Truth_c2w c) Hwr 1 real_1. }
claim Hw1_p : 0 < Truth_c2w c + 1.
{ apply SNoLeLt_tra 0 (Truth_c2w c) (Truth_c2w c + 1) SNo_0 (real_SNo (Truth_c2w c) Hwr) (real_SNo (Truth_c2w c + 1) Hw1_r) Hw0.
  rewrite <- add_SNo_0R (Truth_c2w c) (real_SNo (Truth_c2w c) Hwr) at 1.
  exact add_SNo_Lt2 (Truth_c2w c) 0 1 (real_SNo (Truth_c2w c) Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hw1_ne : Truth_c2w c + 1 <> 0. { exact real_pos_neq0 (Truth_c2w c + 1) (real_SNo (Truth_c2w c + 1) Hw1_r) Hw1_p. }
claim Hq_r : Truth_w2c (Truth_c2w c) :e real. { exact real_div_real (Truth_c2w c) Hwr (Truth_c2w c + 1) Hw1_r Hw1_ne. }
claim Hkey : (Truth_c2w c + 1) * (1 + - c) = 1.
{ rewrite mul_SNo_distrR (Truth_c2w c) 1 (1 + - c) (real_SNo (Truth_c2w c) Hwr) SNo_1 (real_SNo (1 + - c) Hden_r).
  rewrite Truth_c2w_mul c Hc.
  rewrite mul_SNo_oneL (1 + - c) (real_SNo (1 + - c) Hden_r).
  rewrite add_SNo_com 1 (- c) SNo_1 (SNo_minus_SNo c (real_SNo c Hcr)).
  exact add_SNo_minus_L2' c 1 (real_SNo c Hcr) SNo_1. }
apply SNo_mul_cancel_R (Truth_w2c (Truth_c2w c)) c (Truth_c2w c + 1)
      (real_SNo (Truth_w2c (Truth_c2w c)) Hq_r) (real_SNo c Hcr) (real_SNo (Truth_c2w c + 1) Hw1_r) Hw1_ne.
rewrite Truth_w2c_mul (Truth_c2w c) Hw.
apply SNo_mul_cancel_R (Truth_c2w c) (c * (Truth_c2w c + 1)) (1 + - c)
      (real_SNo (Truth_c2w c) Hwr) (SNo_mul_SNo c (Truth_c2w c + 1) (real_SNo c Hcr) (real_SNo (Truth_c2w c + 1) Hw1_r))
      (real_SNo (1 + - c) Hden_r) Hden_ne.
rewrite Truth_c2w_mul c Hc.
rewrite <- mul_SNo_assoc c (Truth_c2w c + 1) (1 + - c) (real_SNo c Hcr) (real_SNo (Truth_c2w c + 1) Hw1_r) (real_SNo (1 + - c) Hden_r).
rewrite Hkey.
symmetry. exact mul_SNo_oneR c (real_SNo c Hcr).
Qed.

Theorem Truth_c2w_w2c_inv : forall w, ValidWeight w -> Truth_c2w (Truth_w2c w) = w.
let w. assume Hw. apply Hw. assume Hwr Hw0.
claim Hw1_r : (w + 1) :e real. { exact real_add_SNo w Hwr 1 real_1. }
claim Hw1_p : 0 < w + 1.
{ apply SNoLeLt_tra 0 w (w + 1) SNo_0 (real_SNo w Hwr) (real_SNo (w + 1) Hw1_r) Hw0.
  rewrite <- add_SNo_0R w (real_SNo w Hwr) at 1.
  exact add_SNo_Lt2 w 0 1 (real_SNo w Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hw1_ne : w + 1 <> 0. { exact real_pos_neq0 (w + 1) (real_SNo (w + 1) Hw1_r) Hw1_p. }
claim Hc : ValidConf (Truth_w2c w). { exact Truth_w2c_valid w Hw. }
claim Hcr : Truth_w2c w :e real. { exact andEL (Truth_w2c w :e real) (0 <= Truth_w2c w) (andEL (Truth_w2c w :e real /\ 0 <= Truth_w2c w) (Truth_w2c w < 1) Hc). }
claim Hc1 : Truth_w2c w < 1. { exact andER (Truth_w2c w :e real /\ 0 <= Truth_w2c w) (Truth_w2c w < 1) Hc. }
claim Hden_r : (1 + - Truth_w2c w) :e real. { exact real_sub 1 real_1 (Truth_w2c w) Hcr. }
claim Hden_p : 0 < 1 + - Truth_w2c w. { exact real_one_minus_pos (Truth_w2c w) Hcr Hc1. }
claim Hden_ne : 1 + - Truth_w2c w <> 0. { exact real_pos_neq0 (1 + - Truth_w2c w) (real_SNo (1 + - Truth_w2c w) Hden_r) Hden_p. }
claim Hq_r : Truth_c2w (Truth_w2c w) :e real. { exact real_div_real (Truth_w2c w) Hcr (1 + - Truth_w2c w) Hden_r Hden_ne. }
claim Hkey : (1 + - Truth_w2c w) * (w + 1) = 1.
{ rewrite mul_SNo_distrR 1 (- Truth_w2c w) (w + 1) SNo_1 (SNo_minus_SNo (Truth_w2c w) (real_SNo (Truth_w2c w) Hcr)) (real_SNo (w + 1) Hw1_r).
  rewrite mul_SNo_oneL (w + 1) (real_SNo (w + 1) Hw1_r).
  rewrite mul_SNo_minus_distrL (Truth_w2c w) (w + 1) (real_SNo (Truth_w2c w) Hcr) (real_SNo (w + 1) Hw1_r).
  rewrite Truth_w2c_mul w Hw.
  rewrite add_SNo_com w 1 (real_SNo w Hwr) SNo_1.
  exact add_SNo_minus_R2 1 w SNo_1 (real_SNo w Hwr). }
apply SNo_mul_cancel_R (Truth_c2w (Truth_w2c w)) w (1 + - Truth_w2c w)
      (real_SNo (Truth_c2w (Truth_w2c w)) Hq_r) (real_SNo w Hwr) (real_SNo (1 + - Truth_w2c w) Hden_r) Hden_ne.
rewrite Truth_c2w_mul (Truth_w2c w) Hc.
apply SNo_mul_cancel_R (Truth_w2c w) (w * (1 + - Truth_w2c w)) (w + 1)
      (real_SNo (Truth_w2c w) Hcr) (SNo_mul_SNo w (1 + - Truth_w2c w) (real_SNo w Hwr) (real_SNo (1 + - Truth_w2c w) Hden_r))
      (real_SNo (w + 1) Hw1_r) Hw1_ne.
rewrite Truth_w2c_mul w Hw.
rewrite <- mul_SNo_assoc w (1 + - Truth_w2c w) (w + 1) (real_SNo w Hwr) (real_SNo (1 + - Truth_w2c w) Hden_r) (real_SNo (w + 1) Hw1_r).
rewrite Hkey.
symmetry. exact mul_SNo_oneR w (real_SNo w Hwr).
Qed.

Theorem Truth_w2c_strict_mono : forall w1 w2, ValidWeight w1 -> ValidWeight w2 -> w1 < w2 -> Truth_w2c w1 < Truth_w2c w2.
let w1 w2. assume Hw1 Hw2 Hlt.
apply Hw1. assume Hw1r Hw10. apply Hw2. assume Hw2r Hw20.
claim H1_r : (w1 + 1) :e real. { exact real_add_SNo w1 Hw1r 1 real_1. }
claim H2_r : (w2 + 1) :e real. { exact real_add_SNo w2 Hw2r 1 real_1. }
claim H1_p : 0 < w1 + 1.
{ apply SNoLeLt_tra 0 w1 (w1 + 1) SNo_0 (real_SNo w1 Hw1r) (real_SNo (w1 + 1) H1_r) Hw10.
  rewrite <- add_SNo_0R w1 (real_SNo w1 Hw1r) at 1.
  exact add_SNo_Lt2 w1 0 1 (real_SNo w1 Hw1r) SNo_0 SNo_1 SNoLt_0_1. }
claim H2_p : 0 < w2 + 1.
{ apply SNoLeLt_tra 0 w2 (w2 + 1) SNo_0 (real_SNo w2 Hw2r) (real_SNo (w2 + 1) H2_r) Hw20.
  rewrite <- add_SNo_0R w2 (real_SNo w2 Hw2r) at 1.
  exact add_SNo_Lt2 w2 0 1 (real_SNo w2 Hw2r) SNo_0 SNo_1 SNoLt_0_1. }
claim H1_ne : w1 + 1 <> 0. { exact real_pos_neq0 (w1 + 1) (real_SNo (w1 + 1) H1_r) H1_p. }
claim H2_ne : w2 + 1 <> 0. { exact real_pos_neq0 (w2 + 1) (real_SNo (w2 + 1) H2_r) H2_p. }
claim Hc1r : Truth_w2c w1 :e real. { exact real_div_real w1 Hw1r (w1 + 1) H1_r H1_ne. }
claim Hc2r : Truth_w2c w2 :e real. { exact real_div_real w2 Hw2r (w2 + 1) H2_r H2_ne. }
claim Hprod_p : 0 < (w1 + 1) * (w2 + 1).
{ exact mul_SNo_pos_pos (w1 + 1) (w2 + 1) (real_SNo (w1 + 1) H1_r) (real_SNo (w2 + 1) H2_r) H1_p H2_p. }
apply SNo_mul_Lt_pos_cancel_R (Truth_w2c w1) (Truth_w2c w2) ((w1 + 1) * (w2 + 1))
      (real_SNo (Truth_w2c w1) Hc1r) (real_SNo (Truth_w2c w2) Hc2r)
      (SNo_mul_SNo (w1 + 1) (w2 + 1) (real_SNo (w1 + 1) H1_r) (real_SNo (w2 + 1) H2_r)) Hprod_p.
claim Hlhs : Truth_w2c w1 * ((w1 + 1) * (w2 + 1)) = w1 * w2 + w1.
{ rewrite mul_SNo_assoc (Truth_w2c w1) (w1 + 1) (w2 + 1) (real_SNo (Truth_w2c w1) Hc1r) (real_SNo (w1 + 1) H1_r) (real_SNo (w2 + 1) H2_r).
  rewrite Truth_w2c_mul w1 Hw1.
  rewrite mul_SNo_distrL w1 w2 1 (real_SNo w1 Hw1r) (real_SNo w2 Hw2r) SNo_1.
  rewrite mul_SNo_oneR w1 (real_SNo w1 Hw1r).
  reflexivity. }
claim Hrhs : Truth_w2c w2 * ((w1 + 1) * (w2 + 1)) = w1 * w2 + w2.
{ rewrite mul_SNo_com (w1 + 1) (w2 + 1) (real_SNo (w1 + 1) H1_r) (real_SNo (w2 + 1) H2_r).
  rewrite mul_SNo_assoc (Truth_w2c w2) (w2 + 1) (w1 + 1) (real_SNo (Truth_w2c w2) Hc2r) (real_SNo (w2 + 1) H2_r) (real_SNo (w1 + 1) H1_r).
  rewrite Truth_w2c_mul w2 Hw2.
  rewrite mul_SNo_distrL w2 w1 1 (real_SNo w2 Hw2r) (real_SNo w1 Hw1r) SNo_1.
  rewrite mul_SNo_com w2 w1 (real_SNo w2 Hw2r) (real_SNo w1 Hw1r).
  rewrite mul_SNo_oneR w2 (real_SNo w2 Hw2r).
  reflexivity. }
rewrite Hlhs. rewrite Hrhs.
exact add_SNo_Lt2 (w1 * w2) w1 w2 (SNo_mul_SNo w1 w2 (real_SNo w1 Hw1r) (real_SNo w2 Hw2r)) (real_SNo w1 Hw1r) (real_SNo w2 Hw2r) Hlt.
Qed.

Theorem Truth_c2w_strict_mono : forall c1 c2, ValidConf c1 -> ValidConf c2 -> c1 < c2 -> Truth_c2w c1 < Truth_c2w c2.
let c1 c2. assume Hc1 Hc2 Hlt.
claim Hw1 : ValidWeight (Truth_c2w c1). { exact Truth_c2w_valid c1 Hc1. }
claim Hw2 : ValidWeight (Truth_c2w c2). { exact Truth_c2w_valid c2 Hc2. }
claim Hw1r : Truth_c2w c1 :e real. { exact andEL (Truth_c2w c1 :e real) (0 <= Truth_c2w c1) Hw1. }
claim Hw2r : Truth_c2w c2 :e real. { exact andEL (Truth_c2w c2 :e real) (0 <= Truth_c2w c2) Hw2. }
apply SNoLt_trichotomy_or (Truth_c2w c1) (Truth_c2w c2) (real_SNo (Truth_c2w c1) Hw1r) (real_SNo (Truth_c2w c2) Hw2r).
- assume Hor. apply Hor.
  + assume H : Truth_c2w c1 < Truth_c2w c2. exact H.
  + assume Heq : Truth_c2w c1 = Truth_c2w c2.
    apply FalseE.
    claim Hceq : c1 = c2.
    { rewrite <- Truth_w2c_c2w_inv c1 Hc1.
      rewrite <- Truth_w2c_c2w_inv c2 Hc2.
      rewrite Heq. reflexivity. }
    apply SNoLt_irref c1.
    rewrite Hceq at 2. exact Hlt.
- assume Hrev : Truth_c2w c2 < Truth_c2w c1.
  apply FalseE.
  claim Hcrev : c2 < c1.
  { rewrite <- Truth_w2c_c2w_inv c1 Hc1.
    rewrite <- Truth_w2c_c2w_inv c2 Hc2.
    exact Truth_w2c_strict_mono (Truth_c2w c2) (Truth_c2w c1) Hw2 Hw1 Hrev. }
  claim Hc1r : c1 :e real. { exact andEL (c1 :e real) (0 <= c1) (andEL (c1 :e real /\ 0 <= c1) (c1 < 1) Hc1). }
  claim Hc2r : c2 :e real. { exact andEL (c2 :e real) (0 <= c2) (andEL (c2 :e real /\ 0 <= c2) (c2 < 1) Hc2). }
  exact SNoLt_irref c1 (SNoLt_tra c1 c2 c1 (real_SNo c1 Hc1r) (real_SNo c2 Hc2r) (real_SNo c1 Hc1r) Hlt Hcrev).
Qed.

(** ---- Theorem Group 2: Closure & Algebraic Properties of NAL Rules -------- *)

Theorem stv_f_pair : forall f c, stv_f (STV f c) = f.
let f c. exact proj0_pair_eq f c.
Qed.

Theorem stv_c_pair : forall f c, stv_c (STV f c) = c.
let f c. exact proj1_pair_eq f c.
Qed.

Theorem ValidFreq_1_minus : forall f, ValidFreq f -> ValidFreq (1 + - f).
let f. assume Hf. apply Hf. assume Hfr0 Hf1. apply Hfr0. assume Hfr Hf0.
apply ValidFreqI.
- exact real_sub 1 real_1 f Hfr.
- exact real_one_minus_nonneg f Hfr Hf1.
- exact real_one_minus_le_1 f Hfr Hf0.
Qed.

Theorem ValidFreq_mul : forall f1 f2, ValidFreq f1 -> ValidFreq f2 -> ValidFreq (f1 * f2).
let f1 f2. assume Hf1 Hf2.
apply Hf1. assume Hf1r0 Hf11. apply Hf1r0. assume Hf1r Hf10.
apply Hf2. assume Hf2r0 Hf21. apply Hf2r0. assume Hf2r Hf20.
apply ValidFreqI.
- exact real_mul_SNo f1 Hf1r f2 Hf2r.
- exact real_unit_prod_nonneg f1 Hf1r f2 Hf2r Hf10 Hf20.
- exact real_unit_prod_le_1 f1 Hf1r f2 Hf2r Hf10 Hf11 Hf20 Hf21.
Qed.

Theorem ValidConf_mul : forall c1 c2, ValidConf c1 -> ValidConf c2 -> ValidConf (c1 * c2).
let c1 c2. assume Hc1 Hc2.
apply Hc1. assume Hc1r0 Hc11. apply Hc1r0. assume Hc1r Hc10.
apply Hc2. assume Hc2r0 Hc21. apply Hc2r0. assume Hc2r Hc20.
apply ValidConfI.
- exact real_mul_SNo c1 Hc1r c2 Hc2r.
- exact real_unit_prod_nonneg c1 Hc1r c2 Hc2r Hc10 Hc20.
- exact real_unit_prod_lt_1 c1 Hc1r c2 Hc2r Hc10 (SNoLtLe c1 1 Hc11) Hc20 Hc21.
Qed.

Theorem ValidFreq_Conf_mul : forall f c, ValidFreq f -> ValidConf c -> ValidConf (f * c).
let f c. assume Hf Hc.
apply Hf. assume Hfr0 Hf1. apply Hfr0. assume Hfr Hf0.
apply Hc. assume Hcr0 Hc1. apply Hcr0. assume Hcr Hc0.
apply ValidConfI.
- exact real_mul_SNo f Hfr c Hcr.
- exact real_unit_prod_nonneg f Hfr c Hcr Hf0 Hc0.
- exact real_unit_prod_lt_1 f Hfr c Hcr Hf0 Hf1 Hc0 Hc1.
Qed.

Theorem Truth_or_valid : forall a b, ValidFreq a -> ValidFreq b -> ValidFreq (Truth_or a b).
let a b. assume Ha Hb.
exact ValidFreq_1_minus ((1 + - a) * (1 + - b))
      (ValidFreq_mul (1 + - a) (1 + - b) (ValidFreq_1_minus a Ha) (ValidFreq_1_minus b Hb)).
Qed.

Theorem ValidSTV_pair : forall f c, ValidFreq f -> ValidConf c -> ValidSTV (STV f c).
let f c. assume Hf Hc.
apply ValidSTVI.
- rewrite stv_f_pair f c. exact Hf.
- rewrite stv_c_pair f c. exact Hc.
Qed.

Theorem Truth_Negation_closed : forall tv, ValidSTV tv -> ValidSTV (Truth_Negation tv).
let tv. assume Htv. apply Htv. assume Hf Hc.
exact ValidSTV_pair (1 + - stv_f tv) (stv_c tv) (ValidFreq_1_minus (stv_f tv) Hf) Hc.
Qed.

Theorem Truth_Negation_invol : forall f c, ValidFreq f -> Truth_Negation (Truth_Negation (STV f c)) = STV f c.
let f c. assume Hf. apply Hf. assume Hfr0 Hf1. apply Hfr0. assume Hfr Hf0.
claim H1 : stv_f (Truth_Negation (STV f c)) = 1 + - f.
{ prove stv_f (STV (1 + - stv_f (STV f c)) (stv_c (STV f c))) = 1 + - f.
  rewrite stv_f_pair (1 + - stv_f (STV f c)) (stv_c (STV f c)).
  rewrite stv_f_pair f c. reflexivity. }
claim H2 : stv_c (Truth_Negation (STV f c)) = c.
{ prove stv_c (STV (1 + - stv_f (STV f c)) (stv_c (STV f c))) = c.
  rewrite stv_c_pair (1 + - stv_f (STV f c)) (stv_c (STV f c)).
  rewrite stv_c_pair f c. reflexivity. }
claim Hinv : 1 + - (1 + - f) = f.
{ rewrite minus_add_SNo_distr 1 (- f) SNo_1 (SNo_minus_SNo f (real_SNo f Hfr)).
  rewrite minus_SNo_invol f (real_SNo f Hfr).
  exact add_SNo_minus_L2' 1 f SNo_1 (real_SNo f Hfr). }
prove STV (1 + - stv_f (Truth_Negation (STV f c))) (stv_c (Truth_Negation (STV f c))) = STV f c.
rewrite H1. rewrite H2. rewrite Hinv.
reflexivity.
Qed.

Theorem Truth_Deduction_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Deduction t1 t2).
let t1 t2. assume H1 H2.
apply H1. assume Hf1 Hc1. apply H2. assume Hf2 Hc2.
exact ValidSTV_pair (stv_f t1 * stv_f t2) ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2))
      (ValidFreq_mul (stv_f t1) (stv_f t2) Hf1 Hf2)
      (ValidFreq_Conf_mul (stv_f t1 * stv_f t2) (stv_c t1 * stv_c t2)
        (ValidFreq_mul (stv_f t1) (stv_f t2) Hf1 Hf2) (ValidConf_mul (stv_c t1) (stv_c t2) Hc1 Hc2)).
Qed.

Theorem Truth_Intersection_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Intersection t1 t2).
let t1 t2. assume H1 H2.
apply H1. assume Hf1 Hc1. apply H2. assume Hf2 Hc2.
exact ValidSTV_pair (stv_f t1 * stv_f t2) (stv_c t1 * stv_c t2)
      (ValidFreq_mul (stv_f t1) (stv_f t2) Hf1 Hf2) (ValidConf_mul (stv_c t1) (stv_c t2) Hc1 Hc2).
Qed.

Theorem Truth_Abduction_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Abduction t1 t2).
let t1 t2. assume H1 H2.
apply H1. assume Hf1 Hc1. apply H2. assume Hf2 Hc2.
claim Hfc : ValidConf (stv_f t1 * stv_c t1). { exact ValidFreq_Conf_mul (stv_f t1) (stv_c t1) Hf1 Hc1. }
claim Hw : ValidConf ((stv_f t1 * stv_c t1) * stv_c t2). { exact ValidConf_mul (stv_f t1 * stv_c t1) (stv_c t2) Hfc Hc2. }
claim Hww : ValidWeight ((stv_f t1 * stv_c t1) * stv_c t2).
{ exact andEL (((stv_f t1 * stv_c t1) * stv_c t2) :e real /\ 0 <= ((stv_f t1 * stv_c t1) * stv_c t2))
              (((stv_f t1 * stv_c t1) * stv_c t2) < 1) Hw. }
exact ValidSTV_pair (stv_f t2) (Truth_w2c ((stv_f t1 * stv_c t1) * stv_c t2))
      Hf2 (Truth_w2c_valid ((stv_f t1 * stv_c t1) * stv_c t2) Hww).
Qed.

Theorem Truth_Induction_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Induction t1 t2).
let t1 t2. assume H1 H2.
exact Truth_Abduction_closed t2 t1 H2 H1.
Qed.

Theorem Truth_Exemplification_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Exemplification t1 t2).
let t1 t2. assume H1 H2.
apply H1. assume Hf1 Hc1. apply H2. assume Hf2 Hc2.
claim Hw : ValidConf ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)).
{ exact ValidFreq_Conf_mul (stv_f t1 * stv_f t2) (stv_c t1 * stv_c t2)
        (ValidFreq_mul (stv_f t1) (stv_f t2) Hf1 Hf2) (ValidConf_mul (stv_c t1) (stv_c t2) Hc1 Hc2). }
claim Hww : ValidWeight ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)).
{ exact andEL (((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)) :e real /\ 0 <= ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)))
              (((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)) < 1) Hw. }
exact ValidSTV_pair 1 (Truth_w2c ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)))
      (ValidFreqI 1 real_1 (SNoLtLe 0 1 SNoLt_0_1) (SNoLe_ref 1))
      (Truth_w2c_valid ((stv_f t1 * stv_f t2) * (stv_c t1 * stv_c t2)) Hww).
Qed.

Theorem Truth_Analogy_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Analogy t1 t2).
let t1 t2. assume H1 H2.
apply H1. assume Hf1 Hc1. apply H2. assume Hf2 Hc2.
claim Hcc : ValidConf (stv_c t1 * stv_c t2). { exact ValidConf_mul (stv_c t1) (stv_c t2) Hc1 Hc2. }
claim Hccf : ValidConf ((stv_c t1 * stv_c t2) * stv_f t2).
{ claim Hccr : (stv_c t1 * stv_c t2) :e real.
  { exact andEL ((stv_c t1 * stv_c t2) :e real) (0 <= (stv_c t1 * stv_c t2)) (andEL ((stv_c t1 * stv_c t2) :e real /\ 0 <= (stv_c t1 * stv_c t2)) ((stv_c t1 * stv_c t2) < 1) Hcc). }
  claim Hf2r : stv_f t2 :e real.
  { exact andEL (stv_f t2 :e real) (0 <= stv_f t2) (andEL (stv_f t2 :e real /\ 0 <= stv_f t2) (stv_f t2 <= 1) Hf2). }
  rewrite mul_SNo_com (stv_c t1 * stv_c t2) (stv_f t2) (real_SNo (stv_c t1 * stv_c t2) Hccr) (real_SNo (stv_f t2) Hf2r).
  exact ValidFreq_Conf_mul (stv_f t2) (stv_c t1 * stv_c t2) Hf2 Hcc. }
exact ValidSTV_pair (stv_f t1 * stv_f t2) ((stv_c t1 * stv_c t2) * stv_f t2)
      (ValidFreq_mul (stv_f t1) (stv_f t2) Hf1 Hf2) Hccf.
Qed.

Theorem Truth_Union_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Union t1 t2).
let t1 t2. assume H1 H2.
apply H1. assume Hf1 Hc1. apply H2. assume Hf2 Hc2.
exact ValidSTV_pair (Truth_or (stv_f t1) (stv_f t2)) (stv_c t1 * stv_c t2)
      (Truth_or_valid (stv_f t1) (stv_f t2) Hf1 Hf2) (ValidConf_mul (stv_c t1) (stv_c t2) Hc1 Hc2).
Qed.

Theorem Truth_Difference_closed : forall t1 t2, ValidSTV t1 -> ValidSTV t2 -> ValidSTV (Truth_Difference t1 t2).
let t1 t2. assume H1 H2.
apply H1. assume Hf1 Hc1. apply H2. assume Hf2 Hc2.
exact ValidSTV_pair (stv_f t1 * (1 + - stv_f t2)) (stv_c t1 * stv_c t2)
      (ValidFreq_mul (stv_f t1) (1 + - stv_f t2) Hf1 (ValidFreq_1_minus (stv_f t2) Hf2))
      (ValidConf_mul (stv_c t1) (stv_c t2) Hc1 Hc2).
Qed.

Theorem Truth_Eternalize_closed : forall tv, ValidSTV tv -> ValidSTV (Truth_Eternalize tv).
let tv. assume Htv. apply Htv. assume Hf Hc.
claim Hw : ValidWeight (stv_c tv).
{ exact andEL (stv_c tv :e real /\ 0 <= stv_c tv) (stv_c tv < 1) Hc. }
exact ValidSTV_pair (stv_f tv) (Truth_w2c (stv_c tv)) Hf (Truth_w2c_valid (stv_c tv) Hw).
Qed.

(** ---- Theorem Group 3: Revision & Tool-Reliability Monotonicity ----------- *)

Theorem Truth_Rev_w_valid : forall c1 c2, ValidConf c1 -> ValidConf c2 -> ValidWeight (Truth_Rev_w c1 c2).
let c1 c2. assume Hc1 Hc2.
claim Hw1 : ValidWeight (Truth_c2w c1). { exact Truth_c2w_valid c1 Hc1. }
claim Hw2 : ValidWeight (Truth_c2w c2). { exact Truth_c2w_valid c2 Hc2. }
apply Hw1. assume Hw1r Hw10. apply Hw2. assume Hw2r Hw20.
apply ValidWeightI.
- exact real_add_SNo (Truth_c2w c1) Hw1r (Truth_c2w c2) Hw2r.
- rewrite <- add_SNo_0L 0 SNo_0.
  exact add_SNo_Le3 0 0 (Truth_c2w c1) (Truth_c2w c2) SNo_0 SNo_0 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo (Truth_c2w c2) Hw2r) Hw10 Hw20.
Qed.

Theorem Truth_Rev_conf_strict_inc : forall c1 c2, ValidConf c1 -> ValidConf c2 -> 0 < c1 -> 0 < c2 ->
  c1 < Truth_Rev_c c1 c2 /\ c2 < Truth_Rev_c c1 c2 /\ Truth_Rev_c c1 c2 < 1.
let c1 c2. assume Hc1 Hc2 Hp1 Hp2.
claim Hw1 : ValidWeight (Truth_c2w c1). { exact Truth_c2w_valid c1 Hc1. }
claim Hw2 : ValidWeight (Truth_c2w c2). { exact Truth_c2w_valid c2 Hc2. }
claim Hw : ValidWeight (Truth_Rev_w c1 c2). { exact Truth_Rev_w_valid c1 c2 Hc1 Hc2. }
apply Hw1. assume Hw1r Hw10. apply Hw2. assume Hw2r Hw20.
claim Hc1r : c1 :e real. { exact andEL (c1 :e real) (0 <= c1) (andEL (c1 :e real /\ 0 <= c1) (c1 < 1) Hc1). }
claim Hc11 : c1 < 1. { exact andER (c1 :e real /\ 0 <= c1) (c1 < 1) Hc1. }
claim Hc2r : c2 :e real. { exact andEL (c2 :e real) (0 <= c2) (andEL (c2 :e real /\ 0 <= c2) (c2 < 1) Hc2). }
claim Hc21 : c2 < 1. { exact andER (c2 :e real /\ 0 <= c2) (c2 < 1) Hc2. }
claim Hw1_pos : 0 < Truth_c2w c1.
{ exact real_div_pos c1 Hc1r (1 + - c1) (real_sub 1 real_1 c1 Hc1r) Hp1 (real_one_minus_pos c1 Hc1r Hc11). }
claim Hw2_pos : 0 < Truth_c2w c2.
{ exact real_div_pos c2 Hc2r (1 + - c2) (real_sub 1 real_1 c2 Hc2r) Hp2 (real_one_minus_pos c2 Hc2r Hc21). }
claim Hlt1 : Truth_c2w c1 < Truth_Rev_w c1 c2.
{ rewrite <- add_SNo_0R (Truth_c2w c1) (real_SNo (Truth_c2w c1) Hw1r) at 1.
  exact add_SNo_Lt2 (Truth_c2w c1) 0 (Truth_c2w c2) (real_SNo (Truth_c2w c1) Hw1r) SNo_0 (real_SNo (Truth_c2w c2) Hw2r) Hw2_pos. }
claim Hlt2 : Truth_c2w c2 < Truth_Rev_w c1 c2.
{ rewrite <- add_SNo_0L (Truth_c2w c2) (real_SNo (Truth_c2w c2) Hw2r) at 1.
  exact add_SNo_Lt1 0 (Truth_c2w c2) (Truth_c2w c1) SNo_0 (real_SNo (Truth_c2w c2) Hw2r) (real_SNo (Truth_c2w c1) Hw1r) Hw1_pos. }
claim Hvc : ValidConf (Truth_Rev_c c1 c2). { exact Truth_w2c_valid (Truth_Rev_w c1 c2) Hw. }
apply and3I.
- rewrite <- Truth_w2c_c2w_inv c1 Hc1 at 1.
  exact Truth_w2c_strict_mono (Truth_c2w c1) (Truth_Rev_w c1 c2) Hw1 Hw Hlt1.
- rewrite <- Truth_w2c_c2w_inv c2 Hc2 at 1.
  exact Truth_w2c_strict_mono (Truth_c2w c2) (Truth_Rev_w c1 c2) Hw2 Hw Hlt2.
- exact andER (Truth_Rev_c c1 c2 :e real /\ 0 <= Truth_Rev_c c1 c2) (Truth_Rev_c c1 c2 < 1) Hvc.
Qed.

Theorem Truth_Rev_comm : forall f1 c1 f2 c2, ValidFreq f1 -> ValidConf c1 -> ValidFreq f2 -> ValidConf c2 ->
  Truth_Rev_f f1 c1 f2 c2 = Truth_Rev_f f2 c2 f1 c1 /\ Truth_Rev_c c1 c2 = Truth_Rev_c c2 c1.
let f1 c1 f2 c2. assume Hf1 Hc1 Hf2 Hc2.
claim Hw1 : ValidWeight (Truth_c2w c1). { exact Truth_c2w_valid c1 Hc1. }
claim Hw2 : ValidWeight (Truth_c2w c2). { exact Truth_c2w_valid c2 Hc2. }
claim Hw1r : Truth_c2w c1 :e real. { exact andEL (Truth_c2w c1 :e real) (0 <= Truth_c2w c1) Hw1. }
claim Hw2r : Truth_c2w c2 :e real. { exact andEL (Truth_c2w c2 :e real) (0 <= Truth_c2w c2) Hw2. }
claim Hf1r : f1 :e real. { exact andEL (f1 :e real) (0 <= f1) (andEL (f1 :e real /\ 0 <= f1) (f1 <= 1) Hf1). }
claim Hf2r : f2 :e real. { exact andEL (f2 :e real) (0 <= f2) (andEL (f2 :e real /\ 0 <= f2) (f2 <= 1) Hf2). }
claim Hw_com : Truth_Rev_w c1 c2 = Truth_Rev_w c2 c1.
{ exact add_SNo_com (Truth_c2w c1) (Truth_c2w c2) (real_SNo (Truth_c2w c1) Hw1r) (real_SNo (Truth_c2w c2) Hw2r). }
apply andI.
- prove (Truth_c2w c1 * f1 + Truth_c2w c2 * f2) :/: Truth_Rev_w c1 c2 =
        (Truth_c2w c2 * f2 + Truth_c2w c1 * f1) :/: Truth_Rev_w c2 c1.
  rewrite Hw_com.
  rewrite add_SNo_com (Truth_c2w c1 * f1) (Truth_c2w c2 * f2)
          (SNo_mul_SNo (Truth_c2w c1) f1 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo f1 Hf1r))
          (SNo_mul_SNo (Truth_c2w c2) f2 (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f2 Hf2r)).
  reflexivity.
- prove Truth_w2c (Truth_Rev_w c1 c2) = Truth_w2c (Truth_Rev_w c2 c1).
  rewrite Hw_com. reflexivity.
Qed.

Theorem Truth_Rev_freq_convex : forall f1 c1 f2 c2,
  ValidFreq f1 -> ValidConf c1 -> ValidFreq f2 -> ValidConf c2 ->
  0 < Truth_Rev_w c1 c2 -> f1 <= f2 ->
  f1 <= Truth_Rev_f f1 c1 f2 c2 /\ Truth_Rev_f f1 c1 f2 c2 <= f2.
let f1 c1 f2 c2. assume Hf1 Hc1 Hf2 Hc2 Hwp Hle.
claim Hw1 : ValidWeight (Truth_c2w c1). { exact Truth_c2w_valid c1 Hc1. }
claim Hw2 : ValidWeight (Truth_c2w c2). { exact Truth_c2w_valid c2 Hc2. }
claim Hw : ValidWeight (Truth_Rev_w c1 c2). { exact Truth_Rev_w_valid c1 c2 Hc1 Hc2. }
apply Hw1. assume Hw1r Hw10. apply Hw2. assume Hw2r Hw20.
apply Hw. assume Hwr Hw0.
claim Hf1r : f1 :e real. { exact andEL (f1 :e real) (0 <= f1) (andEL (f1 :e real /\ 0 <= f1) (f1 <= 1) Hf1). }
claim Hf2r : f2 :e real. { exact andEL (f2 :e real) (0 <= f2) (andEL (f2 :e real /\ 0 <= f2) (f2 <= 1) Hf2). }
claim Hnum_r : (Truth_c2w c1 * f1 + Truth_c2w c2 * f2) :e real.
{ exact real_add_SNo (Truth_c2w c1 * f1) (real_mul_SNo (Truth_c2w c1) Hw1r f1 Hf1r)
                     (Truth_c2w c2 * f2) (real_mul_SNo (Truth_c2w c2) Hw2r f2 Hf2r). }
claim Hwne : Truth_Rev_w c1 c2 <> 0. { exact real_pos_neq0 (Truth_Rev_w c1 c2) (real_SNo (Truth_Rev_w c1 c2) Hwr) Hwp. }
claim Hfr : Truth_Rev_f f1 c1 f2 c2 :e real.
{ exact real_div_real (Truth_c2w c1 * f1 + Truth_c2w c2 * f2) Hnum_r (Truth_Rev_w c1 c2) Hwr Hwne. }
apply andI.
- apply SNo_mul_Le_pos_cancel_R f1 (Truth_Rev_f f1 c1 f2 c2) (Truth_Rev_w c1 c2)
        (real_SNo f1 Hf1r) (real_SNo (Truth_Rev_f f1 c1 f2 c2) Hfr) (real_SNo (Truth_Rev_w c1 c2) Hwr) Hwp.
  prove f1 * Truth_Rev_w c1 c2 <= ((Truth_c2w c1 * f1 + Truth_c2w c2 * f2) :/: Truth_Rev_w c1 c2) * Truth_Rev_w c1 c2.
  rewrite real_div_mul_cancel (Truth_c2w c1 * f1 + Truth_c2w c2 * f2) Hnum_r (Truth_Rev_w c1 c2) Hwr Hwne.
  rewrite mul_SNo_com f1 (Truth_Rev_w c1 c2) (real_SNo f1 Hf1r) (real_SNo (Truth_Rev_w c1 c2) Hwr).
  prove (Truth_c2w c1 + Truth_c2w c2) * f1 <= Truth_c2w c1 * f1 + Truth_c2w c2 * f2.
  rewrite mul_SNo_distrR (Truth_c2w c1) (Truth_c2w c2) f1 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f1 Hf1r).
  apply add_SNo_Le2 (Truth_c2w c1 * f1) (Truth_c2w c2 * f1) (Truth_c2w c2 * f2)
        (SNo_mul_SNo (Truth_c2w c1) f1 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo f1 Hf1r))
        (SNo_mul_SNo (Truth_c2w c2) f1 (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f1 Hf1r))
        (SNo_mul_SNo (Truth_c2w c2) f2 (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f2 Hf2r)).
  rewrite mul_SNo_com (Truth_c2w c2) f1 (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f1 Hf1r).
  rewrite mul_SNo_com (Truth_c2w c2) f2 (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f2 Hf2r).
  exact SNo_mul_Le_pos_R f1 f2 (Truth_c2w c2) (real_SNo f1 Hf1r) (real_SNo f2 Hf2r) (real_SNo (Truth_c2w c2) Hw2r) Hw20 Hle.
- apply SNo_mul_Le_pos_cancel_R (Truth_Rev_f f1 c1 f2 c2) f2 (Truth_Rev_w c1 c2)
        (real_SNo (Truth_Rev_f f1 c1 f2 c2) Hfr) (real_SNo f2 Hf2r) (real_SNo (Truth_Rev_w c1 c2) Hwr) Hwp.
  prove ((Truth_c2w c1 * f1 + Truth_c2w c2 * f2) :/: Truth_Rev_w c1 c2) * Truth_Rev_w c1 c2 <= f2 * Truth_Rev_w c1 c2.
  rewrite real_div_mul_cancel (Truth_c2w c1 * f1 + Truth_c2w c2 * f2) Hnum_r (Truth_Rev_w c1 c2) Hwr Hwne.
  rewrite mul_SNo_com f2 (Truth_Rev_w c1 c2) (real_SNo f2 Hf2r) (real_SNo (Truth_Rev_w c1 c2) Hwr).
  prove Truth_c2w c1 * f1 + Truth_c2w c2 * f2 <= (Truth_c2w c1 + Truth_c2w c2) * f2.
  rewrite mul_SNo_distrR (Truth_c2w c1) (Truth_c2w c2) f2 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f2 Hf2r).
  apply add_SNo_Le1 (Truth_c2w c1 * f1) (Truth_c2w c2 * f2) (Truth_c2w c1 * f2)
        (SNo_mul_SNo (Truth_c2w c1) f1 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo f1 Hf1r))
        (SNo_mul_SNo (Truth_c2w c2) f2 (real_SNo (Truth_c2w c2) Hw2r) (real_SNo f2 Hf2r))
        (SNo_mul_SNo (Truth_c2w c1) f2 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo f2 Hf2r)).
  rewrite mul_SNo_com (Truth_c2w c1) f1 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo f1 Hf1r).
  rewrite mul_SNo_com (Truth_c2w c1) f2 (real_SNo (Truth_c2w c1) Hw1r) (real_SNo f2 Hf2r).
  exact SNo_mul_Le_pos_R f1 f2 (Truth_c2w c1) (real_SNo f1 Hf1r) (real_SNo f2 Hf2r) (real_SNo (Truth_c2w c1) Hw1r) Hw10 Hle.
Qed.

(** Iter Tool-Reliability Monotonicity (lib_reliability.metta:63-67):
   Every tool call strictly increases confidence while staying < 1;
   every success strictly increases f when f < 1; every failure strictly lowers f when f > 0. *)
Theorem Rel_Revise_conf_strict_inc : forall c, ValidConf c -> c < Rel_Revise_c c /\ Rel_Revise_c c < 1.
let c. assume Hc.
claim Hw : ValidWeight (Truth_c2w c). { exact Truth_c2w_valid c Hc. }
apply Hw. assume Hwr Hw0.
claim Hw1 : ValidWeight (Truth_c2w c + 1).
{ apply ValidWeightI.
  - exact real_add_SNo (Truth_c2w c) Hwr 1 real_1.
  - apply SNoLtLe.
    apply SNoLeLt_tra 0 (Truth_c2w c) (Truth_c2w c + 1) SNo_0 (real_SNo (Truth_c2w c) Hwr)
          (SNo_add_SNo (Truth_c2w c) 1 (real_SNo (Truth_c2w c) Hwr) SNo_1) Hw0.
    rewrite <- add_SNo_0R (Truth_c2w c) (real_SNo (Truth_c2w c) Hwr) at 1.
    exact add_SNo_Lt2 (Truth_c2w c) 0 1 (real_SNo (Truth_c2w c) Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hlt : Truth_c2w c < Truth_c2w c + 1.
{ rewrite <- add_SNo_0R (Truth_c2w c) (real_SNo (Truth_c2w c) Hwr) at 1.
  exact add_SNo_Lt2 (Truth_c2w c) 0 1 (real_SNo (Truth_c2w c) Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hvc : ValidConf (Truth_w2c (Truth_c2w c + 1)). { exact Truth_w2c_valid (Truth_c2w c + 1) Hw1. }
apply andI.
- rewrite <- Truth_w2c_c2w_inv c Hc at 1.
  exact Truth_w2c_strict_mono (Truth_c2w c) (Truth_c2w c + 1) Hw Hw1 Hlt.
- exact andER (Truth_w2c (Truth_c2w c + 1) :e real /\ 0 <= Truth_w2c (Truth_c2w c + 1)) (Truth_w2c (Truth_c2w c + 1) < 1) Hvc.
Qed.

Theorem Rel_Revise_success_strict_inc : forall f c, ValidFreq f -> ValidConf c -> f < 1 ->
  f < Rel_Revise_f f c 1 /\ Rel_Revise_f f c 1 <= 1.
let f c. assume Hf Hc Hf1.
apply Hf. assume Hfr0 Hf_le1. apply Hfr0. assume Hfr Hf0.
claim Hw : ValidWeight (Truth_c2w c). { exact Truth_c2w_valid c Hc. }
apply Hw. assume Hwr Hw0.
claim Hsum_r : (Truth_c2w c + 1) :e real. { exact real_add_SNo (Truth_c2w c) Hwr 1 real_1. }
claim Hsum_p : 0 < Truth_c2w c + 1.
{ apply SNoLeLt_tra 0 (Truth_c2w c) (Truth_c2w c + 1) SNo_0 (real_SNo (Truth_c2w c) Hwr) (real_SNo (Truth_c2w c + 1) Hsum_r) Hw0.
  rewrite <- add_SNo_0R (Truth_c2w c) (real_SNo (Truth_c2w c) Hwr) at 1.
  exact add_SNo_Lt2 (Truth_c2w c) 0 1 (real_SNo (Truth_c2w c) Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hsum_ne : Truth_c2w c + 1 <> 0. { exact real_pos_neq0 (Truth_c2w c + 1) (real_SNo (Truth_c2w c + 1) Hsum_r) Hsum_p. }
claim Hnum_r : (Truth_c2w c * f + 1) :e real. { exact real_add_SNo (Truth_c2w c * f) (real_mul_SNo (Truth_c2w c) Hwr f Hfr) 1 real_1. }
claim Hqr : Rel_Revise_f f c 1 :e real. { exact real_div_real (Truth_c2w c * f + 1) Hnum_r (Truth_c2w c + 1) Hsum_r Hsum_ne. }
apply andI.
- apply SNo_mul_Lt_pos_cancel_R f (Rel_Revise_f f c 1) (Truth_c2w c + 1)
        (real_SNo f Hfr) (real_SNo (Rel_Revise_f f c 1) Hqr) (real_SNo (Truth_c2w c + 1) Hsum_r) Hsum_p.
  prove f * (Truth_c2w c + 1) < ((Truth_c2w c * f + 1) :/: (Truth_c2w c + 1)) * (Truth_c2w c + 1).
  rewrite real_div_mul_cancel (Truth_c2w c * f + 1) Hnum_r (Truth_c2w c + 1) Hsum_r Hsum_ne.
  rewrite mul_SNo_com f (Truth_c2w c + 1) (real_SNo f Hfr) (real_SNo (Truth_c2w c + 1) Hsum_r).
  rewrite mul_SNo_distrR (Truth_c2w c) 1 f (real_SNo (Truth_c2w c) Hwr) SNo_1 (real_SNo f Hfr).
  rewrite mul_SNo_oneL f (real_SNo f Hfr).
  exact add_SNo_Lt2 (Truth_c2w c * f) f 1 (SNo_mul_SNo (Truth_c2w c) f (real_SNo (Truth_c2w c) Hwr) (real_SNo f Hfr)) (real_SNo f Hfr) SNo_1 Hf1.
- apply real_div_le_1 (Truth_c2w c * f + 1) Hnum_r (Truth_c2w c + 1) Hsum_r Hsum_p.
  apply add_SNo_Le1 (Truth_c2w c * f) 1 (Truth_c2w c)
        (SNo_mul_SNo (Truth_c2w c) f (real_SNo (Truth_c2w c) Hwr) (real_SNo f Hfr)) SNo_1 (real_SNo (Truth_c2w c) Hwr).
  rewrite mul_SNo_com (Truth_c2w c) f (real_SNo (Truth_c2w c) Hwr) (real_SNo f Hfr).
  rewrite <- mul_SNo_oneL (Truth_c2w c) (real_SNo (Truth_c2w c) Hwr) at 2.
  exact SNo_mul_Le_pos_R f 1 (Truth_c2w c) (real_SNo f Hfr) SNo_1 (real_SNo (Truth_c2w c) Hwr) Hw0 Hf_le1.
Qed.

Theorem Rel_Revise_failure_strict_dec : forall f c, ValidFreq f -> ValidConf c -> 0 < f ->
  0 <= Rel_Revise_f f c 0 /\ Rel_Revise_f f c 0 < f.
let f c. assume Hf Hc Hf0_p.
apply Hf. assume Hfr0 Hf_le1. apply Hfr0. assume Hfr Hf0.
claim Hw : ValidWeight (Truth_c2w c). { exact Truth_c2w_valid c Hc. }
apply Hw. assume Hwr Hw0.
claim Hsum_r : (Truth_c2w c + 1) :e real. { exact real_add_SNo (Truth_c2w c) Hwr 1 real_1. }
claim Hsum_p : 0 < Truth_c2w c + 1.
{ apply SNoLeLt_tra 0 (Truth_c2w c) (Truth_c2w c + 1) SNo_0 (real_SNo (Truth_c2w c) Hwr) (real_SNo (Truth_c2w c + 1) Hsum_r) Hw0.
  rewrite <- add_SNo_0R (Truth_c2w c) (real_SNo (Truth_c2w c) Hwr) at 1.
  exact add_SNo_Lt2 (Truth_c2w c) 0 1 (real_SNo (Truth_c2w c) Hwr) SNo_0 SNo_1 SNoLt_0_1. }
claim Hsum_ne : Truth_c2w c + 1 <> 0. { exact real_pos_neq0 (Truth_c2w c + 1) (real_SNo (Truth_c2w c + 1) Hsum_r) Hsum_p. }
claim Hnum_r : (Truth_c2w c * f + 0) :e real. { exact real_add_SNo (Truth_c2w c * f) (real_mul_SNo (Truth_c2w c) Hwr f Hfr) 0 real_0. }
claim Hqr : Rel_Revise_f f c 0 :e real. { exact real_div_real (Truth_c2w c * f + 0) Hnum_r (Truth_c2w c + 1) Hsum_r Hsum_ne. }
apply andI.
- apply real_div_nonneg (Truth_c2w c * f + 0) Hnum_r (Truth_c2w c + 1) Hsum_r.
  + rewrite add_SNo_0R (Truth_c2w c * f) (SNo_mul_SNo (Truth_c2w c) f (real_SNo (Truth_c2w c) Hwr) (real_SNo f Hfr)).
    exact real_unit_prod_nonneg (Truth_c2w c) Hwr f Hfr Hw0 Hf0.
  + exact Hsum_p.
- apply SNo_mul_Lt_pos_cancel_R (Rel_Revise_f f c 0) f (Truth_c2w c + 1)
        (real_SNo (Rel_Revise_f f c 0) Hqr) (real_SNo f Hfr) (real_SNo (Truth_c2w c + 1) Hsum_r) Hsum_p.
  prove ((Truth_c2w c * f + 0) :/: (Truth_c2w c + 1)) * (Truth_c2w c + 1) < f * (Truth_c2w c + 1).
  rewrite real_div_mul_cancel (Truth_c2w c * f + 0) Hnum_r (Truth_c2w c + 1) Hsum_r Hsum_ne.
  rewrite mul_SNo_com f (Truth_c2w c + 1) (real_SNo f Hfr) (real_SNo (Truth_c2w c + 1) Hsum_r).
  rewrite mul_SNo_distrR (Truth_c2w c) 1 f (real_SNo (Truth_c2w c) Hwr) SNo_1 (real_SNo f Hfr).
  rewrite mul_SNo_oneL f (real_SNo f Hfr).
  exact add_SNo_Lt2 (Truth_c2w c * f) 0 f (SNo_mul_SNo (Truth_c2w c) f (real_SNo (Truth_c2w c) Hwr) (real_SNo f Hfr)) SNo_0 (real_SNo f Hfr) Hf0_p.
Qed.

(** ---- Theorem Group 4: Truth Expectation Properties ----------------------- *)

Theorem half_bounds : half :e real /\ 0 < half /\ half < 1.
claim H2r : (1 + 1) :e real. { exact real_add_SNo 1 real_1 1 real_1. }
claim H1lt2 : 1 < 1 + 1.
{ rewrite <- add_SNo_0R 1 SNo_1 at 1.
  exact add_SNo_Lt2 1 0 1 SNo_1 SNo_0 SNo_1 SNoLt_0_1. }
claim H2p : 0 < 1 + 1. { exact SNoLt_tra 0 1 (1 + 1) SNo_0 SNo_1 (real_SNo (1 + 1) H2r) SNoLt_0_1 H1lt2. }
claim H2ne : 1 + 1 <> 0. { exact real_pos_neq0 (1 + 1) (real_SNo (1 + 1) H2r) H2p. }
apply and3I.
- exact real_div_real 1 real_1 (1 + 1) H2r H2ne.
- exact real_div_pos 1 real_1 (1 + 1) H2r SNoLt_0_1 H2p.
- exact real_div_lt_1 1 real_1 (1 + 1) H2r H2p H1lt2.
Qed.

Theorem half_add_half : half + half = 1.
claim H2r : (1 + 1) :e real. { exact real_add_SNo 1 real_1 1 real_1. }
claim H1lt2 : 1 < 1 + 1.
{ rewrite <- add_SNo_0R 1 SNo_1 at 1.
  exact add_SNo_Lt2 1 0 1 SNo_1 SNo_0 SNo_1 SNoLt_0_1. }
claim H2p : 0 < 1 + 1. { exact SNoLt_tra 0 1 (1 + 1) SNo_0 SNo_1 (real_SNo (1 + 1) H2r) SNoLt_0_1 H1lt2. }
claim H2ne : 1 + 1 <> 0. { exact real_pos_neq0 (1 + 1) (real_SNo (1 + 1) H2r) H2p. }
claim Hhr : half :e real. { exact andEL (half :e real) (0 < half) (andEL (half :e real /\ 0 < half) (half < 1) half_bounds). }
rewrite <- mul_SNo_oneL half (real_SNo half Hhr).
rewrite <- mul_SNo_distrR 1 1 half SNo_1 SNo_1 (real_SNo half Hhr).
rewrite mul_SNo_com (1 + 1) half (real_SNo (1 + 1) H2r) (real_SNo half Hhr).
prove (1 :/: (1 + 1)) * (1 + 1) = 1.
exact real_div_mul_cancel 1 real_1 (1 + 1) H2r H2ne.
Qed.

Theorem Truth_Expectation_zero_conf : forall f, ValidFreq f -> Truth_Expectation f 0 = half.
let f. assume Hf. apply Hf. assume Hfr0 Hf1. apply Hfr0. assume Hfr Hf0.
claim Hhr : half :e real. { exact andEL (half :e real) (0 < half) (andEL (half :e real /\ 0 < half) (half < 1) half_bounds). }
prove 0 * (f + - half) + half = half.
rewrite mul_SNo_zeroL (f + - half) (SNo_add_SNo f (- half) (real_SNo f Hfr) (SNo_minus_SNo half (real_SNo half Hhr))).
exact add_SNo_0L half (real_SNo half Hhr).
Qed.

Theorem Truth_Expectation_convex_form : forall f c, ValidFreq f -> ValidConf c ->
  Truth_Expectation f c = (1 + - c) * half + c * f.
let f c. assume Hf Hc.
apply Hf. assume Hfr0 Hf1. apply Hfr0. assume Hfr Hf0.
apply Hc. assume Hcr0 Hc1. apply Hcr0. assume Hcr Hc0.
claim Hhr : half :e real. { exact andEL (half :e real) (0 < half) (andEL (half :e real /\ 0 < half) (half < 1) half_bounds). }
prove c * (f + - half) + half = (1 + - c) * half + c * f.
rewrite mul_SNo_distrL c f (- half) (real_SNo c Hcr) (real_SNo f Hfr) (SNo_minus_SNo half (real_SNo half Hhr)).
rewrite mul_SNo_minus_distrR c half (real_SNo c Hcr) (real_SNo half Hhr).
rewrite mul_SNo_distrR 1 (- c) half SNo_1 (SNo_minus_SNo c (real_SNo c Hcr)) (real_SNo half Hhr).
rewrite mul_SNo_oneL half (real_SNo half Hhr).
rewrite mul_SNo_minus_distrL c half (real_SNo c Hcr) (real_SNo half Hhr).
rewrite add_SNo_com (half + - (c * half)) (c * f)
        (SNo_add_SNo half (- (c * half)) (real_SNo half Hhr) (SNo_minus_SNo (c * half) (SNo_mul_SNo c half (real_SNo c Hcr) (real_SNo half Hhr))))
        (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr)).
rewrite <- add_SNo_assoc (c * f) (- (c * half)) half
        (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr))
        (SNo_minus_SNo (c * half) (SNo_mul_SNo c half (real_SNo c Hcr) (real_SNo half Hhr)))
        (real_SNo half Hhr).
rewrite add_SNo_com (- (c * half)) half
        (SNo_minus_SNo (c * half) (SNo_mul_SNo c half (real_SNo c Hcr) (real_SNo half Hhr)))
        (real_SNo half Hhr).
reflexivity.
Qed.

Theorem Truth_Expectation_strict_bounds : forall f c, ValidFreq f -> ValidConf c ->
  0 < Truth_Expectation f c /\ Truth_Expectation f c < 1.
let f c. assume Hf Hc.
apply Hf. assume Hfr0 Hf1. apply Hfr0. assume Hfr Hf0.
apply Hc. assume Hcr0 Hc1. apply Hcr0. assume Hcr Hc0.
claim Hhr : half :e real. { exact andEL (half :e real) (0 < half) (andEL (half :e real /\ 0 < half) (half < 1) half_bounds). }
claim Hhp : 0 < half. { exact andER (half :e real) (0 < half) (andEL (half :e real /\ 0 < half) (half < 1) half_bounds). }
claim H1mc_r : (1 + - c) :e real. { exact real_sub 1 real_1 c Hcr. }
claim H1mc_p : 0 < 1 + - c. { exact real_one_minus_pos c Hcr Hc1. }
claim Hterm1_p : 0 < (1 + - c) * half.
{ exact mul_SNo_pos_pos (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr) H1mc_p Hhp. }
claim Hcf_nn : 0 <= c * f. { exact real_unit_prod_nonneg c Hcr f Hfr Hc0 Hf0. }
rewrite Truth_Expectation_convex_form f c Hf Hc.
apply andI.
- apply SNoLtLe_tra 0 ((1 + - c) * half) ((1 + - c) * half + c * f)
        SNo_0 (SNo_mul_SNo (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr))
        (SNo_add_SNo ((1 + - c) * half) (c * f)
          (SNo_mul_SNo (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr))
          (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr))) Hterm1_p.
  rewrite <- add_SNo_0R ((1 + - c) * half) (SNo_mul_SNo (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr)) at 1.
  exact add_SNo_Le2 ((1 + - c) * half) 0 (c * f)
        (SNo_mul_SNo (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr))
        SNo_0 (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr)) Hcf_nn.
- claim Hcf_le_c : c * f <= c.
  { rewrite mul_SNo_com c f (real_SNo c Hcr) (real_SNo f Hfr).
    rewrite <- mul_SNo_oneL c (real_SNo c Hcr) at 2.
    exact SNo_mul_Le_pos_R f 1 c (real_SNo f Hfr) SNo_1 (real_SNo c Hcr) Hc0 Hf1. }
  claim Hhalf_lt_1 : half < 1. { exact andER (half :e real /\ 0 < half) (half < 1) half_bounds. }
  claim Hterm1_lt : (1 + - c) * half < 1 + - c.
  { rewrite mul_SNo_com (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr).
    rewrite <- mul_SNo_oneL (1 + - c) (real_SNo (1 + - c) H1mc_r) at 2.
    exact SNo_mul_Lt_pos_R half 1 (1 + - c) (real_SNo half Hhr) SNo_1 (real_SNo (1 + - c) H1mc_r) H1mc_p Hhalf_lt_1. }
  apply SNoLtLe_tra ((1 + - c) * half + c * f) ((1 + - c) + c * f) 1
        (SNo_add_SNo ((1 + - c) * half) (c * f) (SNo_mul_SNo (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr)) (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr)))
        (SNo_add_SNo (1 + - c) (c * f) (real_SNo (1 + - c) H1mc_r) (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr)))
        SNo_1.
  + exact add_SNo_Lt1 ((1 + - c) * half) (c * f) (1 + - c)
          (SNo_mul_SNo (1 + - c) half (real_SNo (1 + - c) H1mc_r) (real_SNo half Hhr))
          (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr))
          (real_SNo (1 + - c) H1mc_r) Hterm1_lt.
  + claim Hsum1 : (1 + - c) + c = 1.
    { rewrite add_SNo_com (1 + - c) c (real_SNo (1 + - c) H1mc_r) (real_SNo c Hcr).
      rewrite add_SNo_com 1 (- c) SNo_1 (SNo_minus_SNo c (real_SNo c Hcr)).
      exact add_SNo_minus_L2' c 1 (real_SNo c Hcr) SNo_1. }
    rewrite <- Hsum1 at 2.
    exact add_SNo_Le2 (1 + - c) (c * f) c (real_SNo (1 + - c) H1mc_r) (SNo_mul_SNo c f (real_SNo c Hcr) (real_SNo f Hfr)) (real_SNo c Hcr) Hcf_le_c.
Qed.

End IterNALTruth.
