import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.HOL.Semantics.Extensionality
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# HOL World-Model Bridge

This module instantiates the PLN world-model interface on genuine higher-order
Henkin semantics:

- state = multiset of pointed Henkin models,
- query = closed HOL formula,
- evidence = positive/negative support counts from semantic satisfaction.
-/

namespace Mettapedia.Logic.HOL.WorldModel

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev HOLQuery (Const : Ty Base → Type v) := ClosedFormula Const

/-- Closed-formula satisfaction at a pointed Henkin model. -/
def holSatisfies
    (M : HenkinModel.{u, v, w} Base Const) (φ : HOLQuery Const) : Prop :=
  HenkinModel.models M φ

instance : EvidenceType (Multiset (HenkinModel.{u, v, w} Base Const)) where

/-- Evidence extracted from a multiset of pointed Henkin models. -/
noncomputable def holEvidence
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ : HOLQuery Const) : Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun M => holSatisfies M φ) W : ℝ≥0∞),
     (Multiset.countP (fun M => ¬ holSatisfies M φ) W : ℝ≥0∞)⟩

theorem holEvidence_add
    (W₁ W₂ : Multiset (HenkinModel.{u, v, w} Base Const)) (φ : HOLQuery Const) :
    holEvidence (Base := Base) (Const := Const) (W₁ + W₂) φ =
      holEvidence (Base := Base) (Const := Const) W₁ φ +
        holEvidence (Base := Base) (Const := Const) W₂ φ := by
  classical
  apply Evidence.ext'
  · simp [holEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [holEvidence, Multiset.countP_add, Evidence.hplus_def]

/-- World-model instance induced by multiset Henkin evidence counting. -/
noncomputable instance :
    WorldModel (Multiset (HenkinModel.{u, v, w} Base Const)) (HOLQuery Const) where
  evidence := holEvidence (Base := Base) (Const := Const)
  evidence_add := holEvidence_add (Base := Base) (Const := Const)

theorem holEvidence_singleton_of_satisfies
    (M : HenkinModel.{u, v, w} Base Const) (φ : HOLQuery Const) (h : holSatisfies M φ) :
    holEvidence (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = ⟨1, 0⟩ := by
  classical
  ext <;> simp [holEvidence, ← Multiset.cons_zero, h]

theorem holEvidence_singleton_of_not_satisfies
    (M : HenkinModel.{u, v, w} Base Const) (φ : HOLQuery Const) (h : ¬ holSatisfies M φ) :
    holEvidence (Base := Base) (Const := Const)
      ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = ⟨0, 1⟩ := by
  classical
  ext <;> simp [holEvidence, ← Multiset.cons_zero, h]

theorem queryStrength_singleton_of_satisfies
    (M : HenkinModel.{u, v, w} Base Const) (φ : HOLQuery Const) (h : holSatisfies M φ) :
    WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = 1 := by
  change
    Evidence.toStrength
      (holEvidence (Base := Base) (Const := Const)
        ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ) = 1
  rw [holEvidence_singleton_of_satisfies (Base := Base) (Const := Const) M φ h]
  simp [Evidence.toStrength, Evidence.total]

theorem queryStrength_singleton_of_not_satisfies
    (M : HenkinModel.{u, v, w} Base Const) (φ : HOLQuery Const) (h : ¬ holSatisfies M φ) :
    WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = 0 := by
  change
    Evidence.toStrength
      (holEvidence (Base := Base) (Const := Const)
        ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ) = 0
  rw [holEvidence_singleton_of_not_satisfies (Base := Base) (Const := Const) M φ h]
  simp [Evidence.toStrength, Evidence.total]

/-- Singleton adequacy: sentence truth iff singleton query strength is `1`. -/
theorem singleton_adequacy_strength_one
    (M : HenkinModel.{u, v, w} Base Const) (φ : HOLQuery Const) :
    holSatisfies M φ ↔
      WorldModel.queryStrength
          (State := Multiset (HenkinModel.{u, v, w} Base Const))
          (Query := HOLQuery Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies (Base := Base) (Const := Const) M φ h
  · intro h
    by_cases hs : holSatisfies M φ
    · exact hs
    · have h0 :
          WorldModel.queryStrength
              (State := Multiset (HenkinModel.{u, v, w} Base Const))
              (Query := HOLQuery Const)
              ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = 0 :=
        queryStrength_singleton_of_not_satisfies (Base := Base) (Const := Const) M φ hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              WorldModel.queryStrength
                  (State := Multiset (HenkinModel.{u, v, w} Base Const))
                  (Query := HOLQuery Const)
                  ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

theorem pointwiseImplies_iff_singletonStrengthLE (φ ψ : HOLQuery Const) :
    (∀ M : HenkinModel.{u, v, w} Base Const, holSatisfies M φ → holSatisfies M ψ) ↔
      (∀ M : HenkinModel.{u, v, w} Base Const,
        WorldModel.queryStrength
            (State := Multiset (HenkinModel.{u, v, w} Base Const))
            (Query := HOLQuery Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ ≤
          WorldModel.queryStrength
            (State := Multiset (HenkinModel.{u, v, w} Base Const))
            (Query := HOLQuery Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ) := by
  constructor
  · intro himp M
    by_cases hφ : holSatisfies M φ
    · have hψ : holSatisfies M ψ := himp M hφ
      rw [queryStrength_singleton_of_satisfies (Base := Base) (Const := Const) M φ hφ]
      rw [queryStrength_singleton_of_satisfies (Base := Base) (Const := Const) M ψ hψ]
    · rw [queryStrength_singleton_of_not_satisfies (Base := Base) (Const := Const) M φ hφ]
      exact zero_le _
  · intro hle M hφ
    by_contra hψ
    have hsingleton := hle M
    have h1 :
        WorldModel.queryStrength
            (State := Multiset (HenkinModel.{u, v, w} Base Const))
            (Query := HOLQuery Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ = 1 :=
      queryStrength_singleton_of_satisfies (Base := Base) (Const := Const) M φ hφ
    have h0 :
        WorldModel.queryStrength
            (State := Multiset (HenkinModel.{u, v, w} Base Const))
            (Query := HOLQuery Const)
            ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies (Base := Base) (Const := Const) M ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      rw [h1, h0] at htmp
      exact htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

/-- Pointwise semantic equivalence yields world-model query equivalence. -/
theorem queryEq_of_pointwiseIff
    (φ ψ : HOLQuery Const)
    (hiff : ∀ M : HenkinModel.{u, v, w} Base Const, holSatisfies M φ ↔ holSatisfies M ψ) :
    WMQueryEq
      (State := Multiset (HenkinModel.{u, v, w} Base Const))
      (Query := HOLQuery Const) φ ψ := by
  intro W
  classical
  ext <;> simp [WorldModel.evidence, holEvidence, hiff]

/-- Pointwise semantic equivalence yields equality of WM query strengths. -/
theorem queryStrength_eq_of_pointwiseIff
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ ψ : HOLQuery Const)
    (hiff : ∀ M : HenkinModel.{u, v, w} Base Const, holSatisfies M φ ↔ holSatisfies M ψ) :
    WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const) W φ =
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const) W ψ := by
  exact
    WMQueryEq.to_queryStrength
      (State := Multiset (HenkinModel.{u, v, w} Base Const))
      (Query := HOLQuery Const)
      (queryEq_of_pointwiseIff (Base := Base) (Const := Const) φ ψ hiff) W

private theorem countP_le_countP_of_imp
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    {p q : HenkinModel.{u, v, w} Base Const → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ M, p M → q M) :
    Multiset.countP p W ≤ Multiset.countP q W := by
  induction W using Multiset.induction_on with
  | empty =>
      simp
  | @cons a W ih =>
      by_cases hp : p a
      · have hq : q a := himp a hp
        simpa [Multiset.countP_cons_of_pos, hp, hq] using Nat.succ_le_succ ih
      · by_cases hq : q a
        · have hstep : Multiset.countP p W ≤ Multiset.countP q W + 1 :=
            le_trans ih (Nat.le_succ _)
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq] using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih

private theorem holEvidence_total
    (W : Multiset (HenkinModel.{u, v, w} Base Const)) (φ : HOLQuery Const) :
    (holEvidence (Base := Base) (Const := Const) W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W +
          Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => ¬ holSatisfies M φ) W := by
    simpa using
      (Multiset.card_eq_countP_add_countP
        (p := fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => holSatisfies M φ) W : ℝ≥0∞) +
          (Multiset.countP (fun M : HenkinModel.{u, v, w} Base Const => ¬ holSatisfies M φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold holEvidence Evidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to WM strength inequality on multiset states. -/
theorem queryStrength_le_of_pointwise
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ ψ : HOLQuery Const)
    (himp : ∀ M : HenkinModel.{u, v, w} Base Const, holSatisfies M φ → holSatisfies M ψ) :
    WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W φ ≤
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W ψ := by
  let pφ : HenkinModel.{u, v, w} Base Const → Prop := fun M => holSatisfies M φ
  let pψ : HenkinModel.{u, v, w} Base Const → Prop := fun M => holSatisfies M ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      WorldModel.queryStrength
          (State := Multiset (HenkinModel.{u, v, w} Base Const))
          (Query := HOLQuery Const)
          W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change
      (if (holEvidence (Base := Base) (Const := Const) W φ).total = 0 then 0
        else (holEvidence (Base := Base) (Const := Const) W φ).pos /
          (holEvidence (Base := Base) (Const := Const) W φ).total) =
      if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [holEvidence_total (Base := Base) (Const := Const) (W := W) (φ := φ)]
    simp [holEvidence, pφ]
  have hψ :
      WorldModel.queryStrength
          (State := Multiset (HenkinModel.{u, v, w} Base Const))
          (Query := HOLQuery Const)
          W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change
      (if (holEvidence (Base := Base) (Const := Const) W ψ).total = 0 then 0
        else (holEvidence (Base := Base) (Const := Const) W ψ).pos /
          (holEvidence (Base := Base) (Const := Const) W ψ).total) =
      if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [holEvidence_total (Base := Base) (Const := Const) (W := W) (φ := ψ)]
    simp [holEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat : Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp (Base := Base) (Const := Const) (W := W) (p := pφ) (q := pψ) (by
        intro M hp
        exact himp M (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤ (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from singleton-strength assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLE
    (W : Multiset (HenkinModel.{u, v, w} Base Const))
    (φ ψ : HOLQuery Const)
    (hsing : ∀ M : HenkinModel.{u, v, w} Base Const,
      WorldModel.queryStrength
          (State := Multiset (HenkinModel.{u, v, w} Base Const))
          (Query := HOLQuery Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) φ ≤
        WorldModel.queryStrength
          (State := Multiset (HenkinModel.{u, v, w} Base Const))
          (Query := HOLQuery Const)
          ({M} : Multiset (HenkinModel.{u, v, w} Base Const)) ψ) :
    WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W φ ≤
      WorldModel.queryStrength
        (State := Multiset (HenkinModel.{u, v, w} Base Const))
        (Query := HOLQuery Const)
        W ψ := by
  have himp : ∀ M : HenkinModel.{u, v, w} Base Const, holSatisfies M φ → holSatisfies M ψ :=
    (pointwiseImplies_iff_singletonStrengthLE (Base := Base) (Const := Const) φ ψ).mpr hsing
  exact queryStrength_le_of_pointwise (Base := Base) (Const := Const) (W := W) (φ := φ) (ψ := ψ) himp

end Mettapedia.Logic.HOL.WorldModel
