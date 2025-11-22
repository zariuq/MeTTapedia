(* ========================================================================= *)
(* Core Weakness Quantale Theory                                             *)
(* Based on Goertzel's P≠NP proof (arXiv:2510.08814v1)                       *)
(* ========================================================================= *)

(* The weakness quantale is defined on extended naturals: ω ∪ {ω}            *)
(* where ω represents "infinity" (no polytime program exists)                *)

(* --- Omega Regularity --- *)
(* Key axiom: omega is not an element of itself (from set-theoretic regularity) *)
Axiom omega_not_in_omega : omega /:e omega.

(* --- Natural Number Addition Monotonicity --- *)
(* For von Neumann ordinals: a ⊆ b and c ⊆ d implies a+c ⊆ b+d *)
Axiom add_nat_mono_Subq : forall a, nat_p a -> forall b, nat_p b ->
  forall c, nat_p c -> forall d, nat_p d ->
  a c= b -> c c= d -> a + c c= b + d.

(* --- Extended Naturals --- *)

(* ExtNat = ω ∪ {ω}, where ω itself represents infinity *)
Definition ExtNat : set := omega :\/: {omega}.

Definition is_finite_extnat : set -> prop :=
  fun n => n :e omega.

Definition is_infinity : set -> prop :=
  fun n => n = omega.

(* Every element of ExtNat is either finite or infinity *)
Theorem ExtNat_cases : forall n :e ExtNat, is_finite_extnat n \/ is_infinity n.
let n. assume Hn: n :e ExtNat.
prove n :e omega \/ n = omega.
apply binunionE omega {omega} n Hn.
- assume H: n :e omega. apply orIL. exact H.
- assume H: n :e {omega}.
  apply orIR.
  apply UPairE n omega omega H.
  + exact (fun H => H).
  + exact (fun H => H).
Qed.

Theorem finite_in_ExtNat : forall n :e omega, n :e ExtNat.
let n. assume Hn: n :e omega.
apply binunionI1. exact Hn.
Qed.

Theorem infinity_in_ExtNat : omega :e ExtNat.
apply binunionI2.
apply UPairI1.
Qed.

(* Finite and infinity are disjoint *)
Theorem finite_not_infinity : forall n, is_finite_extnat n -> ~is_infinity n.
let n. assume Hfin: is_finite_extnat n.
assume Hinf: is_infinity n.
prove False.
claim L: n = omega. { exact Hinf. }
claim L2: omega :e omega.
{ rewrite <- L. exact Hfin. }
exact (omega_not_in_omega L2).
Qed.

(* --- Quantale Addition --- *)

(* Addition on ExtNat: infinity absorbs everything *)
Definition quant_add : set -> set -> set :=
  fun a b =>
    if is_infinity a then omega
    else if is_infinity b then omega
    else a + b.

(* Infinity is absorbing on the left *)
Theorem quant_add_infinity_l : forall a, quant_add omega a = omega.
let a.
prove (if is_infinity omega then omega else if is_infinity a then omega else omega + a) = omega.
claim L: is_infinity omega. { prove omega = omega. reflexivity. }
exact (If_i_1 (is_infinity omega) omega (if is_infinity a then omega else omega + a) L).
Qed.

(* Infinity is absorbing on the right *)
Theorem quant_add_infinity_r : forall a :e ExtNat, quant_add a omega = omega.
let a. assume Ha: a :e ExtNat.
prove (if is_infinity a then omega else if is_infinity omega then omega else a + omega) = omega.
apply ExtNat_cases a Ha.
- assume Hfin: is_finite_extnat a.
  claim Lnot: ~is_infinity a. { exact (finite_not_infinity a Hfin). }
  rewrite (If_i_0 (is_infinity a) omega (if is_infinity omega then omega else a + omega) Lnot).
  claim Linf: is_infinity omega. { reflexivity. }
  exact (If_i_1 (is_infinity omega) omega (a + omega) Linf).
- assume Hinf: is_infinity a.
  exact (If_i_1 (is_infinity a) omega (if is_infinity omega then omega else a + omega) Hinf).
Qed.

(* Zero is identity *)
Theorem quant_add_0_l : forall a :e ExtNat, quant_add 0 a = a.
let a. assume Ha: a :e ExtNat.
prove (if is_infinity 0 then omega else if is_infinity a then omega else 0 + a) = a.
claim L0: ~is_infinity 0.
{ assume H: 0 = omega.
  claim L: 0 :e omega. { exact (nat_p_omega 0 nat_0). }
  claim L2: omega :e omega. { rewrite <- H. exact L. }
  exact (omega_not_in_omega L2).
}
rewrite (If_i_0 (is_infinity 0) omega (if is_infinity a then omega else 0 + a) L0).
apply ExtNat_cases a Ha.
- assume Hfin: is_finite_extnat a.
  claim Lnot: ~is_infinity a. { exact (finite_not_infinity a Hfin). }
  rewrite (If_i_0 (is_infinity a) omega (0 + a) Lnot).
  prove 0 + a = a.
  exact (add_nat_0L a (omega_nat_p a Hfin)).
- assume Hinf: is_infinity a.
  rewrite (If_i_1 (is_infinity a) omega (0 + a) Hinf).
  prove omega = a.
  symmetry. exact Hinf.
Qed.

(* Commutativity *)
Theorem quant_add_comm : forall a b :e ExtNat, quant_add a b = quant_add b a.
let a b. assume Ha: a :e ExtNat. assume Hb: b :e ExtNat.
apply ExtNat_cases a Ha.
- assume Ha_fin: is_finite_extnat a.
  apply ExtNat_cases b Hb.
  + assume Hb_fin: is_finite_extnat b.
    claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
    claim Lb: ~is_infinity b. { exact (finite_not_infinity b Hb_fin). }
    prove (if is_infinity a then omega else if is_infinity b then omega else a + b) =
          (if is_infinity b then omega else if is_infinity a then omega else b + a).
    rewrite (If_i_0 (is_infinity a) omega (if is_infinity b then omega else a + b) La).
    rewrite (If_i_0 (is_infinity b) omega (a + b) Lb).
    rewrite (If_i_0 (is_infinity b) omega (if is_infinity a then omega else b + a) Lb).
    rewrite (If_i_0 (is_infinity a) omega (b + a) La).
    prove a + b = b + a.
    exact (add_nat_com a (omega_nat_p a Ha_fin) b (omega_nat_p b Hb_fin)).
  + assume Hb_inf: is_infinity b.
    claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
    prove (if is_infinity a then omega else if is_infinity b then omega else a + b) =
          (if is_infinity b then omega else if is_infinity a then omega else b + a).
    rewrite (If_i_0 (is_infinity a) omega (if is_infinity b then omega else a + b) La).
    rewrite (If_i_1 (is_infinity b) omega (a + b) Hb_inf).
    rewrite (If_i_1 (is_infinity b) omega (if is_infinity a then omega else b + a) Hb_inf).
    reflexivity.
- assume Ha_inf: is_infinity a.
  prove (if is_infinity a then omega else if is_infinity b then omega else a + b) =
        (if is_infinity b then omega else if is_infinity a then omega else b + a).
  rewrite (If_i_1 (is_infinity a) omega (if is_infinity b then omega else a + b) Ha_inf).
  apply ExtNat_cases b Hb.
  + assume Hb_fin: is_finite_extnat b.
    claim Lb: ~is_infinity b. { exact (finite_not_infinity b Hb_fin). }
    rewrite (If_i_0 (is_infinity b) omega (if is_infinity a then omega else b + a) Lb).
    rewrite (If_i_1 (is_infinity a) omega (b + a) Ha_inf).
    reflexivity.
  + assume Hb_inf: is_infinity b.
    rewrite (If_i_1 (is_infinity b) omega (if is_infinity a then omega else b + a) Hb_inf).
    reflexivity.
Qed.

(* Associativity *)
Theorem quant_add_assoc : forall a b c :e ExtNat,
  quant_add (quant_add a b) c = quant_add a (quant_add b c).
let a b c. assume Ha: a :e ExtNat. assume Hb: b :e ExtNat. assume Hc: c :e ExtNat.
(* Case analysis on finiteness *)
apply ExtNat_cases a Ha.
- assume Ha_fin: is_finite_extnat a.
  apply ExtNat_cases b Hb.
  + assume Hb_fin: is_finite_extnat b.
    apply ExtNat_cases c Hc.
    * assume Hc_fin: is_finite_extnat c.
      (* All finite: reduces to nat associativity *)
      claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
      claim Lb: ~is_infinity b. { exact (finite_not_infinity b Hb_fin). }
      claim Lc: ~is_infinity c. { exact (finite_not_infinity c Hc_fin). }
      claim Lab: ~is_infinity (a + b).
      { assume H: a + b = omega.
        claim L: a + b :e omega.
        { apply nat_p_omega.
          exact (add_nat_p a (omega_nat_p a Ha_fin) b (omega_nat_p b Hb_fin)). }
        claim L2: omega :e omega. { rewrite <- H. exact L. }
        exact (omega_not_in_omega L2).
      }
      claim Lbc: ~is_infinity (b + c).
      { assume H: b + c = omega.
        claim L: b + c :e omega.
        { apply nat_p_omega.
          exact (add_nat_p b (omega_nat_p b Hb_fin) c (omega_nat_p c Hc_fin)). }
        claim L2: omega :e omega. { rewrite <- H. exact L. }
        exact (omega_not_in_omega L2).
      }
      (* Expand quant_add definitions *)
      prove (if is_infinity (quant_add a b) then omega else
             if is_infinity c then omega else quant_add a b + c) =
            (if is_infinity a then omega else
             if is_infinity (quant_add b c) then omega else a + quant_add b c).
      (* Simplify LHS: quant_add a b = a + b *)
      claim Leq_ab: quant_add a b = a + b.
      { prove (if is_infinity a then omega else if is_infinity b then omega else a + b) = a + b.
        rewrite (If_i_0 (is_infinity a) omega (if is_infinity b then omega else a + b) La).
        rewrite (If_i_0 (is_infinity b) omega (a + b) Lb).
        reflexivity. }
      (* Simplify RHS: quant_add b c = b + c *)
      claim Leq_bc: quant_add b c = b + c.
      { prove (if is_infinity b then omega else if is_infinity c then omega else b + c) = b + c.
        rewrite (If_i_0 (is_infinity b) omega (if is_infinity c then omega else b + c) Lb).
        rewrite (If_i_0 (is_infinity c) omega (b + c) Lc).
        reflexivity. }
      rewrite Leq_ab. rewrite Leq_bc.
      rewrite (If_i_0 (is_infinity (a + b)) omega (if is_infinity c then omega else (a + b) + c) Lab).
      rewrite (If_i_0 (is_infinity c) omega ((a + b) + c) Lc).
      rewrite (If_i_0 (is_infinity a) omega (if is_infinity (b + c) then omega else a + (b + c)) La).
      rewrite (If_i_0 (is_infinity (b + c)) omega (a + (b + c)) Lbc).
      prove (a + b) + c = a + (b + c).
      exact (add_nat_asso a (omega_nat_p a Ha_fin) b (omega_nat_p b Hb_fin) c (omega_nat_p c Hc_fin)).
    * assume Hc_inf: is_infinity c.
      (* c = infinity: both sides = infinity *)
      claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
      claim Lb: ~is_infinity b. { exact (finite_not_infinity b Hb_fin). }
      claim Leq_ab: quant_add a b = a + b.
      { prove (if is_infinity a then omega else if is_infinity b then omega else a + b) = a + b.
        rewrite (If_i_0 (is_infinity a) omega (if is_infinity b then omega else a + b) La).
        rewrite (If_i_0 (is_infinity b) omega (a + b) Lb).
        reflexivity. }
      claim Lab: ~is_infinity (a + b).
      { assume H: a + b = omega.
        claim L: a + b :e omega.
        { apply nat_p_omega.
          exact (add_nat_p a (omega_nat_p a Ha_fin) b (omega_nat_p b Hb_fin)). }
        claim L2: omega :e omega. { rewrite <- H. exact L. }
        exact (omega_not_in_omega L2). }
      claim Leq_bc: quant_add b c = omega.
      { prove (if is_infinity b then omega else if is_infinity c then omega else b + c) = omega.
        rewrite (If_i_0 (is_infinity b) omega (if is_infinity c then omega else b + c) Lb).
        exact (If_i_1 (is_infinity c) omega (b + c) Hc_inf). }
      prove quant_add (quant_add a b) c = quant_add a (quant_add b c).
      rewrite Leq_ab. rewrite Leq_bc.
      prove quant_add (a + b) c = quant_add a omega.
      prove (if is_infinity (a + b) then omega else if is_infinity c then omega else (a + b) + c) =
            (if is_infinity a then omega else if is_infinity omega then omega else a + omega).
      rewrite (If_i_0 (is_infinity (a + b)) omega (if is_infinity c then omega else (a + b) + c) Lab).
      rewrite (If_i_1 (is_infinity c) omega ((a + b) + c) Hc_inf).
      rewrite (If_i_0 (is_infinity a) omega (if is_infinity omega then omega else a + omega) La).
      claim Linf_omega: is_infinity omega. { reflexivity. }
      rewrite (If_i_1 (is_infinity omega) omega (a + omega) Linf_omega).
      reflexivity.
  + assume Hb_inf: is_infinity b.
    (* b = infinity: both sides = infinity *)
    claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
    claim Leq_ab: quant_add a b = omega.
    { prove (if is_infinity a then omega else if is_infinity b then omega else a + b) = omega.
      rewrite (If_i_0 (is_infinity a) omega (if is_infinity b then omega else a + b) La).
      exact (If_i_1 (is_infinity b) omega (a + b) Hb_inf). }
    claim Leq_bc: quant_add b c = omega.
    { exact (quant_add_infinity_l c). }
    prove quant_add (quant_add a b) c = quant_add a (quant_add b c).
    rewrite Leq_ab. rewrite Leq_bc.
    prove quant_add omega c = quant_add a omega.
    rewrite (quant_add_infinity_l c).
    rewrite (quant_add_infinity_r a Ha).
    reflexivity.
- assume Ha_inf: is_infinity a.
  (* a = infinity: both sides = infinity *)
  prove quant_add (quant_add a b) c = quant_add a (quant_add b c).
  rewrite (quant_add_infinity_l b).
  rewrite (quant_add_infinity_l c).
  rewrite (quant_add_infinity_l (quant_add b c)).
  reflexivity.
Qed.

(* --- Quantale Ordering --- *)

(* Ordering on ExtNat: standard order, with infinity greatest *)
Definition quant_le : set -> set -> prop :=
  fun a b =>
    (is_finite_extnat a /\ is_finite_extnat b /\ a c= b) \/
    (is_finite_extnat a /\ is_infinity b) \/
    (is_infinity a /\ is_infinity b).

(* Reflexivity *)
Theorem quant_le_refl : forall a :e ExtNat, quant_le a a.
let a. assume Ha: a :e ExtNat.
apply ExtNat_cases a Ha.
- assume Hfin: is_finite_extnat a.
  apply orIL.
  apply andI. exact Hfin.
  apply andI. exact Hfin.
  prove a c= a. exact (Subq_ref a).
- assume Hinf: is_infinity a.
  apply orIR. apply orIR.
  apply andI. exact Hinf. exact Hinf.
Qed.

(* Infinity is greatest *)
Theorem quant_le_infinity : forall a :e ExtNat, quant_le a omega.
let a. assume Ha: a :e ExtNat.
apply ExtNat_cases a Ha.
- assume Hfin: is_finite_extnat a.
  apply orIR. apply orIL.
  apply andI. exact Hfin.
  prove is_infinity omega. reflexivity.
- assume Hinf: is_infinity a.
  apply orIR. apply orIR.
  apply andI. exact Hinf.
  prove is_infinity omega. reflexivity.
Qed.

(* Transitivity *)
Theorem quant_le_trans : forall a b c :e ExtNat,
  quant_le a b -> quant_le b c -> quant_le a c.
let a b c. assume Ha: a :e ExtNat. assume Hb: b :e ExtNat. assume Hc: c :e ExtNat.
assume Hab: quant_le a b.
assume Hbc: quant_le b c.
apply Hab.
- assume H1: is_finite_extnat a /\ is_finite_extnat b /\ a c= b.
  apply H1. assume Ha_fin: is_finite_extnat a. assume H1'.
  apply H1'. assume Hb_fin: is_finite_extnat b. assume Hab_sub: a c= b.
  apply Hbc.
  + assume H2: is_finite_extnat b /\ is_finite_extnat c /\ b c= c.
    apply H2. assume _. assume H2'. apply H2'. assume Hc_fin: is_finite_extnat c. assume Hbc_sub: b c= c.
    apply orIL. apply andI. exact Ha_fin. apply andI. exact Hc_fin.
    prove a c= c. exact (Subq_tra a b c Hab_sub Hbc_sub).
  + assume H2: (is_finite_extnat b /\ is_infinity c) \/ (is_infinity b /\ is_infinity c).
    apply H2.
    * assume H3: is_finite_extnat b /\ is_infinity c.
      apply H3. assume _. assume Hc_inf: is_infinity c.
      apply orIR. apply orIL. apply andI. exact Ha_fin. exact Hc_inf.
    * assume H3: is_infinity b /\ is_infinity c.
      apply H3. assume Hb_inf: is_infinity b. assume _.
      apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
- assume H1: (is_finite_extnat a /\ is_infinity b) \/ (is_infinity a /\ is_infinity b).
  apply H1.
  + assume H2: is_finite_extnat a /\ is_infinity b.
    apply H2. assume Ha_fin: is_finite_extnat a. assume Hb_inf: is_infinity b.
    apply Hbc.
    * assume H3: is_finite_extnat b /\ is_finite_extnat c /\ b c= c.
      apply H3. assume Hb_fin: is_finite_extnat b. assume _.
      apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
    * assume H3: (is_finite_extnat b /\ is_infinity c) \/ (is_infinity b /\ is_infinity c).
      apply H3.
      -- assume H4: is_finite_extnat b /\ is_infinity c.
         apply H4. assume Hb_fin: is_finite_extnat b. assume _.
         apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
      -- assume H4: is_infinity b /\ is_infinity c.
         apply H4. assume _. assume Hc_inf: is_infinity c.
         apply orIR. apply orIL. apply andI. exact Ha_fin. exact Hc_inf.
  + assume H2: is_infinity a /\ is_infinity b.
    apply H2. assume Ha_inf: is_infinity a. assume Hb_inf: is_infinity b.
    apply Hbc.
    * assume H3: is_finite_extnat b /\ is_finite_extnat c /\ b c= c.
      apply H3. assume Hb_fin: is_finite_extnat b. assume _.
      apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
    * assume H3: (is_finite_extnat b /\ is_infinity c) \/ (is_infinity b /\ is_infinity c).
      apply H3.
      -- assume H4: is_finite_extnat b /\ is_infinity c.
         apply H4. assume Hb_fin: is_finite_extnat b. assume _.
         apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
      -- assume H4: is_infinity b /\ is_infinity c.
         apply H4. assume _. assume Hc_inf: is_infinity c.
         apply orIR. apply orIR. apply andI. exact Ha_inf. exact Hc_inf.
Qed.

(* Antisymmetry *)
Theorem quant_le_antisym : forall a b :e ExtNat,
  quant_le a b -> quant_le b a -> a = b.
let a b. assume Ha: a :e ExtNat. assume Hb: b :e ExtNat.
assume Hab: quant_le a b.
assume Hba: quant_le b a.
apply Hab.
- assume H1: is_finite_extnat a /\ is_finite_extnat b /\ a c= b.
  apply H1. assume Ha_fin: is_finite_extnat a. assume H1'.
  apply H1'. assume Hb_fin: is_finite_extnat b. assume Hab_sub: a c= b.
  apply Hba.
  + assume H2: is_finite_extnat b /\ is_finite_extnat a /\ b c= a.
    apply H2. assume _. assume H2'. apply H2'. assume _. assume Hba_sub: b c= a.
    prove a = b. exact (set_ext a b Hab_sub Hba_sub).
  + assume H2: (is_finite_extnat b /\ is_infinity a) \/ (is_infinity b /\ is_infinity a).
    apply H2.
    * assume H3: is_finite_extnat b /\ is_infinity a.
      apply H3. assume _. assume Ha_inf: is_infinity a.
      apply False_rect. exact (finite_not_infinity a Ha_fin Ha_inf).
    * assume H3: is_infinity b /\ is_infinity a.
      apply H3. assume Hb_inf: is_infinity b. assume _.
      apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
- assume H1: (is_finite_extnat a /\ is_infinity b) \/ (is_infinity a /\ is_infinity b).
  apply H1.
  + assume H2: is_finite_extnat a /\ is_infinity b.
    apply H2. assume Ha_fin: is_finite_extnat a. assume Hb_inf: is_infinity b.
    apply Hba.
    * assume H3: is_finite_extnat b /\ is_finite_extnat a /\ b c= a.
      apply H3. assume Hb_fin: is_finite_extnat b. assume _.
      apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
    * assume H3: (is_finite_extnat b /\ is_infinity a) \/ (is_infinity b /\ is_infinity a).
      apply H3.
      -- assume H4: is_finite_extnat b /\ is_infinity a.
         apply H4. assume Hb_fin: is_finite_extnat b. assume _.
         apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
      -- assume H4: is_infinity b /\ is_infinity a.
         apply H4. assume _. assume Ha_inf: is_infinity a.
         apply False_rect. exact (finite_not_infinity a Ha_fin Ha_inf).
  + assume H2: is_infinity a /\ is_infinity b.
    apply H2. assume Ha_inf: is_infinity a. assume Hb_inf: is_infinity b.
    prove a = b.
    claim La: a = omega. { exact Ha_inf. }
    claim Lb: b = omega. { exact Hb_inf. }
    rewrite La. rewrite Lb. reflexivity.
Qed.

(* Addition is monotonic in both arguments *)
Theorem quant_add_mono : forall a b c d :e ExtNat,
  quant_le a b -> quant_le c d -> quant_le (quant_add a c) (quant_add b d).
let a b c d. assume Ha: a :e ExtNat. assume Hb: b :e ExtNat.
assume Hc: c :e ExtNat. assume Hd: d :e ExtNat.
assume Hab: quant_le a b.
assume Hcd: quant_le c d.
(* First check if b or d is infinity - then RHS is infinity so quant_le holds *)
apply ExtNat_cases b Hb.
- assume Hb_fin: is_finite_extnat b.
  apply ExtNat_cases d Hd.
  + assume Hd_fin: is_finite_extnat d.
    (* Both b and d are finite, so a and c must be finite too *)
    apply Hab.
    * assume H1: is_finite_extnat a /\ is_finite_extnat b /\ a c= b.
      apply H1. assume Ha_fin: is_finite_extnat a. assume H1'.
      apply H1'. assume _. assume Hab_sub: a c= b.
      apply Hcd.
      -- assume H2: is_finite_extnat c /\ is_finite_extnat d /\ c c= d.
         apply H2. assume Hc_fin: is_finite_extnat c. assume H2'.
         apply H2'. assume _. assume Hcd_sub: c c= d.
         (* All four are finite: use nat monotonicity *)
         claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
         claim Lb: ~is_infinity b. { exact (finite_not_infinity b Hb_fin). }
         claim Lc: ~is_infinity c. { exact (finite_not_infinity c Hc_fin). }
         claim Ld: ~is_infinity d. { exact (finite_not_infinity d Hd_fin). }
         claim Lac: quant_add a c = a + c.
         { prove (if is_infinity a then omega else if is_infinity c then omega else a + c) = a + c.
           rewrite (If_i_0 (is_infinity a) omega (if is_infinity c then omega else a + c) La).
           rewrite (If_i_0 (is_infinity c) omega (a + c) Lc).
           reflexivity. }
         claim Lbd: quant_add b d = b + d.
         { prove (if is_infinity b then omega else if is_infinity d then omega else b + d) = b + d.
           rewrite (If_i_0 (is_infinity b) omega (if is_infinity d then omega else b + d) Lb).
           rewrite (If_i_0 (is_infinity d) omega (b + d) Ld).
           reflexivity. }
         rewrite Lac. rewrite Lbd.
         claim Hac_fin: is_finite_extnat (a + c).
         { prove a + c :e omega. apply nat_p_omega.
           exact (add_nat_p a (omega_nat_p a Ha_fin) c (omega_nat_p c Hc_fin)). }
         claim Hbd_fin: is_finite_extnat (b + d).
         { prove b + d :e omega. apply nat_p_omega.
           exact (add_nat_p b (omega_nat_p b Hb_fin) d (omega_nat_p d Hd_fin)). }
         apply orIL. apply andI. exact Hac_fin. apply andI. exact Hbd_fin.
         prove a + c c= b + d.
         exact (add_nat_mono_Subq a (omega_nat_p a Ha_fin) b (omega_nat_p b Hb_fin)
                c (omega_nat_p c Hc_fin) d (omega_nat_p d Hd_fin) Hab_sub Hcd_sub).
      -- assume H2: (is_finite_extnat c /\ is_infinity d) \/ (is_infinity c /\ is_infinity d).
         apply H2.
         ++ assume H3: is_finite_extnat c /\ is_infinity d.
            apply H3. assume _. assume Hd_inf: is_infinity d.
            apply False_rect. exact (finite_not_infinity d Hd_fin Hd_inf).
         ++ assume H3: is_infinity c /\ is_infinity d.
            apply H3. assume _. assume Hd_inf: is_infinity d.
            apply False_rect. exact (finite_not_infinity d Hd_fin Hd_inf).
    * assume H1: (is_finite_extnat a /\ is_infinity b) \/ (is_infinity a /\ is_infinity b).
      apply H1.
      -- assume H2: is_finite_extnat a /\ is_infinity b.
         apply H2. assume _. assume Hb_inf: is_infinity b.
         apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
      -- assume H2: is_infinity a /\ is_infinity b.
         apply H2. assume _. assume Hb_inf: is_infinity b.
         apply False_rect. exact (finite_not_infinity b Hb_fin Hb_inf).
  + assume Hd_inf: is_infinity d.
    (* d = infinity: RHS is infinity *)
    claim Lb: ~is_infinity b. { exact (finite_not_infinity b Hb_fin). }
    claim Lbd_eq: quant_add b d = omega.
    { prove (if is_infinity b then omega else if is_infinity d then omega else b + d) = omega.
      rewrite (If_i_0 (is_infinity b) omega (if is_infinity d then omega else b + d) Lb).
      exact (If_i_1 (is_infinity d) omega (b + d) Hd_inf). }
    rewrite Lbd_eq.
    claim Hac_in_ExtNat: quant_add a c :e ExtNat.
    { apply ExtNat_cases a Ha.
      - assume Ha_fin: is_finite_extnat a.
        apply ExtNat_cases c Hc.
        + assume Hc_fin: is_finite_extnat c.
          claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
          claim Lc: ~is_infinity c. { exact (finite_not_infinity c Hc_fin). }
          claim Lac: quant_add a c = a + c.
          { prove (if is_infinity a then omega else if is_infinity c then omega else a + c) = a + c.
            rewrite (If_i_0 (is_infinity a) omega (if is_infinity c then omega else a + c) La).
            rewrite (If_i_0 (is_infinity c) omega (a + c) Lc).
            reflexivity. }
          rewrite Lac.
          apply finite_in_ExtNat. apply nat_p_omega.
          exact (add_nat_p a (omega_nat_p a Ha_fin) c (omega_nat_p c Hc_fin)).
        + assume Hc_inf: is_infinity c.
          claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
          claim Lac: quant_add a c = omega.
          { prove (if is_infinity a then omega else if is_infinity c then omega else a + c) = omega.
            rewrite (If_i_0 (is_infinity a) omega (if is_infinity c then omega else a + c) La).
            exact (If_i_1 (is_infinity c) omega (a + c) Hc_inf). }
          rewrite Lac. exact infinity_in_ExtNat.
      - assume Ha_inf: is_infinity a.
        rewrite (quant_add_infinity_l c). exact infinity_in_ExtNat.
    }
    exact (quant_le_infinity (quant_add a c) Hac_in_ExtNat).
- assume Hb_inf: is_infinity b.
  (* b = infinity: RHS is infinity *)
  claim Lbd_eq: quant_add b d = omega. { exact (quant_add_infinity_l d). }
  rewrite Lbd_eq.
  claim Hac_in_ExtNat: quant_add a c :e ExtNat.
  { apply ExtNat_cases a Ha.
    - assume Ha_fin: is_finite_extnat a.
      apply ExtNat_cases c Hc.
      + assume Hc_fin: is_finite_extnat c.
        claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
        claim Lc: ~is_infinity c. { exact (finite_not_infinity c Hc_fin). }
        claim Lac: quant_add a c = a + c.
        { prove (if is_infinity a then omega else if is_infinity c then omega else a + c) = a + c.
          rewrite (If_i_0 (is_infinity a) omega (if is_infinity c then omega else a + c) La).
          rewrite (If_i_0 (is_infinity c) omega (a + c) Lc).
          reflexivity. }
        rewrite Lac.
        apply finite_in_ExtNat. apply nat_p_omega.
        exact (add_nat_p a (omega_nat_p a Ha_fin) c (omega_nat_p c Hc_fin)).
      + assume Hc_inf: is_infinity c.
        claim La: ~is_infinity a. { exact (finite_not_infinity a Ha_fin). }
        claim Lac: quant_add a c = omega.
        { prove (if is_infinity a then omega else if is_infinity c then omega else a + c) = omega.
          rewrite (If_i_0 (is_infinity a) omega (if is_infinity c then omega else a + c) La).
          exact (If_i_1 (is_infinity c) omega (a + c) Hc_inf). }
        rewrite Lac. exact infinity_in_ExtNat.
    - assume Ha_inf: is_infinity a.
      rewrite (quant_add_infinity_l c). exact infinity_in_ExtNat.
  }
  exact (quant_le_infinity (quant_add a c) Hac_in_ExtNat).
Qed.

(* ========================================================================= *)
(* The Weakness Measure K^poly                                               *)
(* ========================================================================= *)

(* These require a computation model, which we axiomatize *)
Parameter UTM_computes : set -> set -> set -> prop.
Parameter UTM_halts_in : set -> set -> set -> prop.
Parameter desc_length : set -> set.
Parameter exp_nat : set -> set -> set.

(* K^poly(z|y) = minimum description length of polytime program computing z from y *)
Definition Kpoly : set -> set -> set :=
  fun z y =>
    Eps_i (fun k =>
      k :e ExtNat /\
      ((is_finite_extnat k /\
        exists p, desc_length p = k /\
                  UTM_computes p y z /\
                  exists c :e omega, UTM_halts_in p y (exp_nat (desc_length y) c)) \/
       (is_infinity k /\
        ~exists p, UTM_computes p y z /\
                   exists c :e omega, UTM_halts_in p y (exp_nat (desc_length y) c)))).

(* Weakness = K^poly *)
Definition weakness : set -> set -> set := Kpoly.

(* K^poly is always in ExtNat *)
Axiom Kpoly_in_ExtNat : forall z y, Kpoly z y :e ExtNat.

(* --- Key Properties of Kpoly (as axioms since they require computation theory) --- *)

(* Chain rule: K(x,z|y) ≤ K(x|y) + K(z|x,y) + O(1) *)
Axiom Kpoly_chain_rule : forall x z y,
  exists c :e omega,
    quant_le (Kpoly (x, z) y)
             (quant_add (quant_add (Kpoly x y) (Kpoly z (x, y))) c).

(* Monotonicity: more context can only help *)
Axiom Kpoly_monotonicity : forall x y z,
  exists c :e omega,
    quant_le (Kpoly x (z, y)) (quant_add (Kpoly x y) c).

(* Subadditivity *)
Axiom Kpoly_subadditive : forall x y,
  exists c :e omega,
    quant_le (Kpoly (x, y) Empty)
             (quant_add (quant_add (Kpoly x Empty) (Kpoly y Empty)) c).

(* ========================================================================= *)
(* Quantale Structure Summary                                                *)
(* ========================================================================= *)

(* The triple (ExtNat, quant_add, quant_le) forms a quantale:
   - (ExtNat, quant_add, 0) is a commutative monoid
   - quant_le is a partial order
   - quant_add is monotonic w.r.t. quant_le
   - omega is the top element

   This allows algebraic manipulation of complexity bounds. *)
