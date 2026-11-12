(** Lean's decision of a bounded quantifier, one step: the second equation of
    Nat.decidableBallLT.

    "For all x below n + 1" holds exactly when it holds for all x below n and
    at n.  A decision is determined by the truth of its proposition
    (Library/DecisionTruth.mg), so Lean's case analysis on the two smaller
    decisions is the canonical decision of the larger proposition. **)

(** For all x below b, P x. **)
Definition LeanNatBall : set -> set -> set := fun b P =>
  Pi_ x :e Lean_Nat, (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0)).

Theorem LeanNatBall_prop : forall b P,
  (forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) -> P x 0 :e LeanProp) -> LeanNatBall b P :e LeanProp.
let b P. assume HP: forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) -> P x 0 :e LeanProp.
prove (Pi_ x :e Lean_Nat, (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0))) :e LeanProp.
apply LeanPi_prop Lean_Nat (fun x => (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0))).
let x. assume Hx: x :e Lean_Nat.
prove (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0)) :e LeanProp.
apply LeanPi_prop (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) (fun h => (P x 0)).
let h. assume Hh: h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b).
exact HP x Hx (Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node x) b) h Hh).
Qed.

Theorem LeanNatBall_intro : forall b P,
  (forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) -> 0 :e P x 0) -> 0 :e LeanNatBall b P.
let b P. assume H: forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) -> 0 :e P x 0.
prove 0 :e (Pi_ x :e Lean_Nat, (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0))).
apply Pi_0_In Lean_Nat (fun x => (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0))).
let x. assume Hx: x :e Lean_Nat.
prove 0 :e (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0)).
apply Pi_0_In (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) (fun h => (P x 0)).
let h. assume Hh: h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b).
exact H x Hx (Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node x) b) h Hh).
Qed.

Theorem LeanNatBall_elim : forall b P, 0 :e LeanNatBall b P ->
  forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) -> P x 0 :e LeanProp -> 0 :e P x 0.
let b P. assume H: 0 :e LeanNatBall b P. let x. assume Hx: x :e Lean_Nat.
assume Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b). assume Hprop: P x 0 :e LeanProp.
claim A0: 0 x :e (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0)).
{ exact ap_Pi Lean_Nat (fun x => (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b), (P x 0))) 0 x H Hx. }
claim A1: 0 x 0 :e (P x 0).
{ exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node x) b) (fun h => (P x 0)) (0 x) 0 A0 Hle. }
exact Lean_prop_0_of (P x 0) Hprop (0 x 0) A1.
Qed.

(** The bounded quantifier at a successor. **)
Theorem LeanNatBall_succ_below : forall n :e Lean_Nat, forall P,
  (forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)) -> P x 0 :e LeanProp) ->
  0 :e LeanNatBall (Lean_Nat_succ_node n) P -> 0 :e LeanNatBall n P.
let n. assume Hn: n :e Lean_Nat. let P.
assume HP: forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)) -> P x 0 :e LeanProp.
assume H: 0 :e LeanNatBall (Lean_Nat_succ_node n) P.
apply LeanNatBall_intro n P.
let x. assume Hx: x :e Lean_Nat. assume Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n).
claim Hle2: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)).
{ exact LeanNat_le_succ_right (Lean_Nat_succ_node x) (Lean_Nat_succ_typed x Hx) n Hn Hle. }
exact LeanNatBall_elim (Lean_Nat_succ_node n) P H x Hx Hle2 (HP x Hx Hle2).
Qed.

Theorem LeanNatBall_succ_at : forall n :e Lean_Nat, forall P,
  (forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)) -> P x 0 :e LeanProp) ->
  0 :e LeanNatBall (Lean_Nat_succ_node n) P -> 0 :e P n 0.
let n. assume Hn: n :e Lean_Nat. let P.
assume HP: forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)) -> P x 0 :e LeanProp.
assume H: 0 :e LeanNatBall (Lean_Nat_succ_node n) P.
claim Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node n) (Lean_Nat_succ_node n)).
{ exact Lean_Nat_le_refl_proof_ok (Lean_Nat_succ_node n). }
exact LeanNatBall_elim (Lean_Nat_succ_node n) P H n Hn Hle (HP n Hn Hle).
Qed.

Theorem LeanNatBall_succ_intro : forall n :e Lean_Nat, forall P,
  (forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)) -> P x 0 :e LeanProp) ->
  0 :e LeanNatBall n P -> 0 :e P n 0 -> 0 :e LeanNatBall (Lean_Nat_succ_node n) P.
let n. assume Hn: n :e Lean_Nat. let P.
assume HP: forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)) -> P x 0 :e LeanProp.
assume Hbelow: 0 :e LeanNatBall n P. assume Hat: 0 :e P n 0.
apply LeanNatBall_intro (Lean_Nat_succ_node n) P.
let x. assume Hx: x :e Lean_Nat. assume Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node n)).
apply Lean_Nat_num x Hx. let j. assume Hj: nat_p j /\ x = LeanNum j.
apply Hj. assume Hj1: nat_p j. assume Hj2: x = LeanNum j.
apply Lean_Nat_num n Hn. let k. assume Hk: nat_p k /\ n = LeanNum k.
apply Hk. assume Hk1: nat_p k. assume Hk2: n = LeanNum k.
claim Lsub: ordsucc j c= ordsucc k.
{ apply Lean_Nat_le_num_Subq (ordsucc j) (nat_ordsucc j Hj1) (ordsucc k) (nat_ordsucc k Hk1).
  rewrite LeanNum_S j Hj1. rewrite LeanNum_S k Hk1.
  rewrite <- Hj2. rewrite <- Hk2. exact Hle. }
apply ordsuccE k j (Lsub j (ordsuccI2 j)).
- assume Hjk: j :e k.
  claim Hle2: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n).
  { rewrite Hj2. rewrite Hk2. rewrite <- LeanNum_S j Hj1.
    exact Lean_Nat_le_num_of_Subq (ordsucc j) (nat_ordsucc j Hj1) k Hk1
      (ordinal_ordsucc_In_Subq k (nat_p_ordinal k Hk1) j Hjk). }
  exact LeanNatBall_elim n P Hbelow x Hx Hle2 (HP x Hx Hle).
- assume Hjk: j = k.
  claim Exn: x = n.
  { rewrite Hj2. rewrite Hk2. rewrite Hjk. reflexivity. }
  rewrite Exn. exact Hat.
Qed.

(** The predicate restricted to a smaller bound gives the same proposition. **)
Theorem LeanNatBall_restrict : forall n, forall P,
  LeanNatBall n (fun x1 :e Lean_Nat => (fun x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x1) n) => (P x1 0))) = LeanNatBall n P.
let n P.
prove (Pi_ x :e Lean_Nat, (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n), ((fun x1 :e Lean_Nat => (fun x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x1) n) => (P x1 0))) x 0)))
  = (Pi_ x :e Lean_Nat, (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n), (P x 0))).
apply Pi_family_eq Lean_Nat
  (fun x => (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n), ((fun x1 :e Lean_Nat => (fun x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x1) n) => (P x1 0))) x 0)))
  (fun x => (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n), (P x 0))).
let x. assume Hx: x :e Lean_Nat.
prove (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n), ((fun x1 :e Lean_Nat => (fun x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x1) n) => (P x1 0))) x 0))
  = (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n), (P x 0)).
apply Pi_family_eq (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n)
  (fun h => ((fun x1 :e Lean_Nat => (fun x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x1) n) => (P x1 0))) x 0))
  (fun h => (P x 0)).
let h. assume Hh: h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n).
prove (fun x1 :e Lean_Nat => (fun x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x1) n) => (P x1 0))) x 0 = P x 0.
rewrite beta Lean_Nat (fun x1 => (fun x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x1) n) => (P x1 0))) x Hx.
exact beta (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n) (fun x2 => (P x 0)) 0
  (Lean_prop_0_of (Lean_Nat_le_Prop (Lean_Nat_succ_node x) n) (Lean_Nat_le_Prop_prop (Lean_Nat_succ_node x) n) h Hh).
Qed.

(** Lean's equation Nat.decidableBallLT.eq_2, for the reading. **)
Theorem LeanNatBall_decision_step : forall v_n :e Lean_Nat, forall v_P :e (Pi_ v_k :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_k) (Lean_Nat_add v_n (LeanNum 1))), LeanProp)), forall v_H :e (Pi_ v_x3 :e Lean_Nat, (Pi_ v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x3) (Lean_Nat_add v_n (LeanNum 1))), (Lean_Decidable (v_P v_x3 0)))), (Lean_Nat_decidableBallLT (Lean_Nat_succ_node v_n) v_P v_H) = (Lean_Decidable_rec (Pi_ v_x6 :e Lean_Nat, (Pi_ v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x6) v_n), (v_P v_x6 0))) (fun v_h :e (Pi_ ux :e (Pi_ v_x6 :e Lean_Nat, (Pi_ v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x6) v_n), (v_P v_x6 0))), Lean_False_Prop) => (Lean_Decidable_isFalse_node (Pi_ v_x4 :e Lean_Nat, (Pi_ v_x5 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x4) (Lean_Nat_add v_n (LeanNum 1))), (v_P v_x4 0))) 0)) (fun v_h :e (Pi_ v_x6 :e Lean_Nat, (Pi_ v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x6) v_n), (v_P v_x6 0))) => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (Pi_ v_x5 :e Lean_Nat, (Pi_ v_x6 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x5) (Lean_Nat_add v_n (LeanNum 1))), (v_P v_x5 0))) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (Pi_ v_x5 :e Lean_Nat, (Pi_ v_x6 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x5) (Lean_Nat_add v_n (LeanNum 1))), (v_P v_x5 0))) 0)) (v_H v_n 0))) (Lean_Nat_decidableBallLT v_n (fun v_x1 :e Lean_Nat => (fun v_x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x1) v_n) => (v_P v_x1 0))) (fun v_x3 :e Lean_Nat => (fun v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x3) v_n) => (v_H v_x3 0))))).
let v_n. assume Hn: v_n :e Lean_Nat.
let v_P. assume HP: v_P :e (Pi_ v_k :e Lean_Nat, (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_k) (Lean_Nat_add v_n (LeanNum 1))), LeanProp)).
let v_H. assume HH: v_H :e (Pi_ v_x3 :e Lean_Nat, (Pi_ v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x3) (Lean_Nat_add v_n (LeanNum 1))), (Lean_Decidable (v_P v_x3 0)))).
claim Hfib: forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node v_n)) -> v_P x 0 :e LeanProp.
{ let x. assume Hx: x :e Lean_Nat. assume Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node v_n)).
  claim Hle2: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_add v_n (LeanNum 1))).
  { rewrite LeanNat_add_one v_n Hn. exact Hle. }
  exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_add v_n (LeanNum 1))) (fun ux => LeanProp) (v_P x) 0
    (ap_Pi Lean_Nat (fun v_k => (Pi_ ux :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_k) (Lean_Nat_add v_n (LeanNum 1))), LeanProp)) v_P x HP Hx) Hle2. }
claim Hfib_below: forall x :e Lean_Nat, 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) v_n) -> v_P x 0 :e LeanProp.
{ let x. assume Hx: x :e Lean_Nat. assume Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) v_n).
  exact Hfib x Hx (LeanNat_le_succ_right (Lean_Nat_succ_node x) (Lean_Nat_succ_typed x Hx) v_n Hn Hle). }
claim Hat_le: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n) (Lean_Nat_succ_node v_n)).
{ exact Lean_Nat_le_refl_proof_ok (Lean_Nat_succ_node v_n). }
claim Hat_le2: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n) (Lean_Nat_add v_n (LeanNum 1))).
{ rewrite LeanNat_add_one v_n Hn. exact Hat_le. }
claim HQp: (LeanNatBall v_n v_P) :e LeanProp.
{ exact LeanNatBall_prop v_n v_P Hfib_below. }
claim HPn: (v_P v_n 0) :e LeanProp.
{ exact Hfib v_n Hn Hat_le. }
claim HHn: (v_H v_n 0) :e Lean_Decidable (v_P v_n 0).
{ exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node v_n) (Lean_Nat_add v_n (LeanNum 1))) (fun v_h => (Lean_Decidable (v_P v_n 0))) (v_H v_n) 0
    (ap_Pi Lean_Nat (fun v_x3 => (Pi_ v_h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x3) (Lean_Nat_add v_n (LeanNum 1))), (Lean_Decidable (v_P v_x3 0)))) v_H v_n HH Hn) Hat_le2. }
prove Lean_DecCanon (LeanNatBall (Lean_Nat_succ_node v_n) v_P)
  = (Lean_Decidable_rec (LeanNatBall v_n v_P) (fun v_h :e (Pi_ ux :e (LeanNatBall v_n v_P), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_add v_n (LeanNum 1)) v_P) 0)) (fun v_h :e (LeanNatBall v_n v_P) => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_add v_n (LeanNum 1)) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_add v_n (LeanNum 1)) v_P) 0)) (v_H v_n 0))) (Lean_DecCanon (LeanNatBall v_n (fun v_x1 :e Lean_Nat => (fun v_x2 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node v_x1) v_n) => (v_P v_x1 0)))))).
rewrite LeanNatBall_restrict v_n v_P.
rewrite LeanNat_add_one v_n Hn.
apply Lean_Decidable_truth (LeanNatBall v_n v_P) HQp (Lean_DecCanon (LeanNatBall v_n v_P)) (Lean_DecCanon_In (LeanNatBall v_n v_P) HQp)
  (fun e => Lean_DecCanon (LeanNatBall (Lean_Nat_succ_node v_n) v_P) = (Lean_Decidable_rec (LeanNatBall v_n v_P) (fun v_h :e (Pi_ ux :e (LeanNatBall v_n v_P), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (LeanNatBall v_n v_P) => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (v_H v_n 0))) e)).
- assume Hbelow: 0 :e (LeanNatBall v_n v_P).
  prove Lean_DecCanon (LeanNatBall (Lean_Nat_succ_node v_n) v_P) = (Lean_Decidable_rec (LeanNatBall v_n v_P) (fun v_h :e (Pi_ ux :e (LeanNatBall v_n v_P), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (LeanNatBall v_n v_P) => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (v_H v_n 0))) (Lean_Decidable_isTrue_node (LeanNatBall v_n v_P) 0)).
  rewrite Lean_Decidable_iota1 (LeanNatBall v_n v_P) (fun v_h :e (Pi_ ux :e (LeanNatBall v_n v_P), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (LeanNatBall v_n v_P) => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (v_H v_n 0))) 0 Hbelow.
  rewrite beta (LeanNatBall v_n v_P) (fun v_h => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (v_H v_n 0))) 0 Hbelow.
  apply Lean_Decidable_truth (v_P v_n 0) HPn (v_H v_n 0) HHn
    (fun e => Lean_DecCanon (LeanNatBall (Lean_Nat_succ_node v_n) v_P) = (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) e)).
  + assume Hat: 0 :e (v_P v_n 0).
    prove Lean_DecCanon (LeanNatBall (Lean_Nat_succ_node v_n) v_P) = (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (Lean_Decidable_isTrue_node (v_P v_n 0) 0)).
    rewrite Lean_Decidable_iota1 (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) 0 Hat.
    rewrite beta (v_P v_n 0) (fun v_h => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) 0 Hat.
    exact Lean_DecCanon_true (LeanNatBall (Lean_Nat_succ_node v_n) v_P) (LeanNatBall_succ_intro v_n Hn v_P Hfib Hbelow Hat).
  + assume Hnat: 0 /:e (v_P v_n 0).
    prove Lean_DecCanon (LeanNatBall (Lean_Nat_succ_node v_n) v_P) = (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (Lean_Decidable_isFalse_node (v_P v_n 0) 0)).
    rewrite Lean_Decidable_iota0 (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) 0 (Lean_refute_0 (v_P v_n 0) HPn Hnat).
    rewrite beta (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) (fun v_h => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) 0 (Lean_refute_0 (v_P v_n 0) HPn Hnat).
    exact Lean_DecCanon_false (LeanNatBall (Lean_Nat_succ_node v_n) v_P)
      (fun Hall: 0 :e (LeanNatBall (Lean_Nat_succ_node v_n) v_P) => Hnat (LeanNatBall_succ_at v_n Hn v_P Hfib Hall)).
- assume Hnbelow: 0 /:e (LeanNatBall v_n v_P).
  prove Lean_DecCanon (LeanNatBall (Lean_Nat_succ_node v_n) v_P) = (Lean_Decidable_rec (LeanNatBall v_n v_P) (fun v_h :e (Pi_ ux :e (LeanNatBall v_n v_P), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (LeanNatBall v_n v_P) => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (v_H v_n 0))) (Lean_Decidable_isFalse_node (LeanNatBall v_n v_P) 0)).
  rewrite Lean_Decidable_iota0 (LeanNatBall v_n v_P) (fun v_h :e (Pi_ ux :e (LeanNatBall v_n v_P), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (LeanNatBall v_n v_P) => (Lean_Decidable_rec (v_P v_n 0) (fun v_h :e (Pi_ ux :e (v_P v_n 0), Lean_False_Prop) => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (fun v_h :e (v_P v_n 0) => (Lean_Decidable_isTrue_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) (v_H v_n 0))) 0 (Lean_refute_0 (LeanNatBall v_n v_P) HQp Hnbelow).
  rewrite beta (Pi_ ux :e (LeanNatBall v_n v_P), Lean_False_Prop) (fun v_h => (Lean_Decidable_isFalse_node (LeanNatBall (Lean_Nat_succ_node v_n) v_P) 0)) 0 (Lean_refute_0 (LeanNatBall v_n v_P) HQp Hnbelow).
  exact Lean_DecCanon_false (LeanNatBall (Lean_Nat_succ_node v_n) v_P)
    (fun Hall: 0 :e (LeanNatBall (Lean_Nat_succ_node v_n) v_P) => Hnbelow (LeanNatBall_succ_below v_n Hn v_P Hfib Hall)).
Qed.

(** Positive and negative examples: nothing is below zero, so every predicate
    holds below zero; and a predicate that fails at zero does not hold below one. **)
Theorem LeanNatBall_zero_ex : forall P, 0 :e LeanNatBall (LeanNum 0) P.
let P.
apply LeanNatBall_intro (LeanNum 0) P.
let x. assume Hx: x :e Lean_Nat. assume Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (LeanNum 0)).
exact FalseE (LeanNat_not_below_zero x Hx Hle) (0 :e P x 0).
Qed.

Theorem LeanNatBall_one_ex_not : 0 /:e LeanNatBall (Lean_Nat_succ_node (LeanNum 0))
  (fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)).
assume H: 0 :e LeanNatBall (Lean_Nat_succ_node (LeanNum 0))
  (fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)).
claim Hle: 0 :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (Lean_Nat_succ_node (LeanNum 0))).
{ exact Lean_Nat_le_refl_proof_ok (Lean_Nat_succ_node (LeanNum 0)). }
claim A0: 0 (LeanNum 0) :e (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (Lean_Nat_succ_node (LeanNum 0))),
  ((fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)) (LeanNum 0) 0)).
{ exact ap_Pi Lean_Nat (fun x => (Pi_ h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))),
    ((fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)) x 0)))
    0 (LeanNum 0) H (LeanNum_In 0 nat_0). }
claim A1: 0 (LeanNum 0) 0 :e ((fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)) (LeanNum 0) 0).
{ exact ap_Pi (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (Lean_Nat_succ_node (LeanNum 0)))
    (fun h => ((fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)) (LeanNum 0) 0))
    (0 (LeanNum 0)) 0 A0 Hle. }
claim E: (fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)) (LeanNum 0) 0 = Lean_False_Prop.
{ rewrite beta Lean_Nat (fun x => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)) (LeanNum 0) (LeanNum_In 0 nat_0).
  exact beta (Lean_Nat_le_Prop (Lean_Nat_succ_node (LeanNum 0)) (Lean_Nat_succ_node (LeanNum 0))) (fun h => Lean_False_Prop) 0 Hle. }
exact Lean_False_Prop_empty (0 (LeanNum 0) 0) (In_eq_r (0 (LeanNum 0) 0)
  ((fun x :e Lean_Nat => (fun h :e (Lean_Nat_le_Prop (Lean_Nat_succ_node x) (Lean_Nat_succ_node (LeanNum 0))) => Lean_False_Prop)) (LeanNum 0) 0)
  Lean_False_Prop E A1).
Qed.
