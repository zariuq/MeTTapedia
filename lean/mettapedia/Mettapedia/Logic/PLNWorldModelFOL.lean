import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelCrispSpecialization
import Mettapedia.Logic.PLNWorldModel
import Foundation.FirstOrder.Basic

/-!
# First-Order (Foundation Sentence) Instance for the WM Calculus

This module instantiates `WorldModel` on Foundation first-order semantics:

- state = multiset of first-order structures (`Struc L`),
- query = first-order sentence (`Sentence L`),
- evidence = positive/negative support counts from Tarskian satisfaction.

Singleton states recover crisp 0/1 query strength.
-/

namespace Mettapedia.Logic.PLNWorldModelFOL

open LO
open LO.FirstOrder
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe u

abbrev FOLQuery (L : Language.{u}) := Sentence L
abbrev PointedFOL (L : Language.{u}) := SmallStruc L

/-- Sentence satisfaction at a pointed first-order structure. -/
def folSatisfies {L : Language.{u}} (S : PointedFOL L) (φ : FOLQuery L) : Prop :=
  Semantics.Models S φ

instance {L : Language.{u}} : EvidenceType (Multiset (PointedFOL L)) where

/-- Evidence extracted from a multiset of pointed FOL structures:
`pos` counts models of `φ`, `neg` counts refutations of `φ`. -/
noncomputable def folEvidence {L : Language.{u}}
    (W : Multiset (PointedFOL L)) (φ : FOLQuery L) : Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun S => folSatisfies S φ) W : ℝ≥0∞),
     (Multiset.countP (fun S => ¬ folSatisfies S φ) W : ℝ≥0∞)⟩

/-- The FOL bridge is a direct instance of the generic crisp-specialization
evidence extractor. -/
theorem folEvidence_eq_crispEvidence {L : Language.{u}}
    (W : Multiset (PointedFOL L)) (φ : FOLQuery L) :
    folEvidence W φ =
      Mettapedia.Logic.PLNWorldModelCrispSpecialization.crispEvidence
        folSatisfies W φ := by
  rfl

theorem folEvidence_add {L : Language.{u}}
    (W₁ W₂ : Multiset (PointedFOL L)) (φ : FOLQuery L) :
    folEvidence (W₁ + W₂) φ = folEvidence W₁ φ + folEvidence W₂ φ := by
  classical
  apply Evidence.ext'
  · simp [folEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [folEvidence, Multiset.countP_add, Evidence.hplus_def]

/-- Concrete `WorldModel` instance induced by multiset FOL evidence counting. -/
noncomputable instance {L : Language.{u}} : WorldModel (Multiset (PointedFOL L)) (FOLQuery L) where
  evidence := folEvidence
  evidence_add := folEvidence_add

theorem folEvidence_singleton_of_satisfies {L : Language.{u}}
    (S : PointedFOL L) (φ : FOLQuery L) (h : folSatisfies S φ) :
    folEvidence ({S} : Multiset (PointedFOL L)) φ = ⟨1, 0⟩ := by
  classical
  ext <;> simp [folEvidence, ← Multiset.cons_zero, h]

theorem folEvidence_singleton_of_not_satisfies {L : Language.{u}}
    (S : PointedFOL L) (φ : FOLQuery L) (h : ¬ folSatisfies S φ) :
    folEvidence ({S} : Multiset (PointedFOL L)) φ = ⟨0, 1⟩ := by
  classical
  ext <;> simp [folEvidence, ← Multiset.cons_zero, h]

/-- Singleton WM states recover crisp 0/1 query strength from sentence truth. -/
theorem queryStrength_singleton_of_satisfies {L : Language.{u}}
    (S : PointedFOL L) (φ : FOLQuery L) (h : folSatisfies S φ) :
    WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
        ({S} : Multiset (PointedFOL L)) φ = 1 := by
  change Evidence.toStrength (folEvidence ({S} : Multiset (PointedFOL L)) φ) = 1
  rw [folEvidence_singleton_of_satisfies S φ h]
  simp [Evidence.toStrength, Evidence.total]

theorem queryStrength_singleton_of_not_satisfies {L : Language.{u}}
    (S : PointedFOL L) (φ : FOLQuery L) (h : ¬ folSatisfies S φ) :
    WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
        ({S} : Multiset (PointedFOL L)) φ = 0 := by
  change Evidence.toStrength (folEvidence ({S} : Multiset (PointedFOL L)) φ) = 0
  rw [folEvidence_singleton_of_not_satisfies S φ h]
  simp [Evidence.toStrength, Evidence.total]

/-- Singleton adequacy: first-order sentence truth iff WM query strength is `1`. -/
theorem singleton_adequacy_strength_one {L : Language.{u}}
    (S : PointedFOL L) (φ : FOLQuery L) :
    folSatisfies S φ ↔
      WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
        ({S} : Multiset (PointedFOL L)) φ = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies S φ h
  · intro h
    by_cases hs : folSatisfies S φ
    · exact hs
    · have h0 :
          WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
              ({S} : Multiset (PointedFOL L)) φ = 0 :=
        queryStrength_singleton_of_not_satisfies S φ hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
                ({S} : Multiset (PointedFOL L)) φ := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-- Explicit witness that the singleton adequacy theorem for the FOL bridge is
an instance of the generic crisp-specialization theorem family. -/
theorem singleton_adequacy_strength_one_is_crispSpecialization {L : Language.{u}}
    (S : PointedFOL L) (φ : FOLQuery L) :
    folSatisfies S φ ↔
      WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
        ({S} : Multiset (PointedFOL L)) φ = 1 := by
  simpa [Mettapedia.Logic.PLNWorldModelCrispSpecialization.crispQueryStrength,
    WorldModel.queryStrength, folEvidence_eq_crispEvidence]
    using
      (Mettapedia.Logic.PLNWorldModelCrispSpecialization.singleton_adequacy_strength_one
        (satisfies := folSatisfies) S φ)

/-! ## Consequence adequacy on singleton and multiset FOL states -/

/-- Singleton-strength consequence schema for FOL WM states. -/
def singletonStrengthLE {L : Language.{u}} (φ ψ : FOLQuery L) : Prop :=
  ∀ S : PointedFOL L,
    WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
        ({S} : Multiset (PointedFOL L)) φ ≤
      WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
        ({S} : Multiset (PointedFOL L)) ψ

/-- Pointwise semantic implication is equivalent to singleton-strength consequence. -/
theorem pointwiseImplies_iff_singletonStrengthLE {L : Language.{u}}
    (φ ψ : FOLQuery L) :
    (∀ S : PointedFOL L, folSatisfies S φ → folSatisfies S ψ) ↔
      singletonStrengthLE φ ψ := by
  constructor
  · intro himp S
    by_cases hφ : folSatisfies S φ
    · have hψ : folSatisfies S ψ := himp S hφ
      rw [queryStrength_singleton_of_satisfies S φ hφ]
      rw [queryStrength_singleton_of_satisfies S ψ hψ]
    · rw [queryStrength_singleton_of_not_satisfies S φ hφ]
      exact zero_le _
  · intro hle S hφ
    by_contra hψ
    have hsingleton := hle S
    have h1 :
        WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
            ({S} : Multiset (PointedFOL L)) φ = 1 :=
      queryStrength_singleton_of_satisfies S φ hφ
    have h0 :
        WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L)
            ({S} : Multiset (PointedFOL L)) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies S ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      rw [h1, h0] at htmp
      exact htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp {L : Language.{u}}
    (W : Multiset (PointedFOL L))
    {p q : PointedFOL L → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ S, p S → q S) :
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
          simpa [Multiset.countP_cons_of_neg, hp, Multiset.countP_cons_of_pos, hq]
            using hstep
        · simpa [Multiset.countP_cons_of_neg, hp, hq] using ih

private theorem folEvidence_total {L : Language.{u}}
    (W : Multiset (PointedFOL L)) (φ : FOLQuery L) :
    (folEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun S : PointedFOL L => folSatisfies S φ) W +
          Multiset.countP (fun S : PointedFOL L => ¬ folSatisfies S φ) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun S : PointedFOL L => folSatisfies S φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun S : PointedFOL L => folSatisfies S φ) W : ℝ≥0∞) +
          (Multiset.countP (fun S : PointedFOL L => ¬ folSatisfies S φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold folEvidence Evidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to WM strength inequality on multiset states. -/
theorem queryStrength_le_of_pointwise {L : Language.{u}}
    (W : Multiset (PointedFOL L)) (φ ψ : FOLQuery L)
    (himp : ∀ S : PointedFOL L, folSatisfies S φ → folSatisfies S ψ) :
    WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W φ ≤
      WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W ψ := by
  let pφ : PointedFOL L → Prop := fun S => folSatisfies S φ
  let pψ : PointedFOL L → Prop := fun S => folSatisfies S ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (folEvidence W φ).total = 0 then 0
      else (folEvidence W φ).pos / (folEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [folEvidence_total (W := W) (φ := φ)]
    simp [folEvidence, pφ]
  have hψ :
      WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (folEvidence W ψ).total = 0 then 0
      else (folEvidence W ψ).pos / (folEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [folEvidence_total (W := W) (φ := ψ)]
    simp [folEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp (W := W) (p := pφ) (q := pψ) (by
        intro S hp
        exact himp S (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from singleton-strength assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLE {L : Language.{u}}
    (W : Multiset (PointedFOL L)) (φ ψ : FOLQuery L)
    (hsing : singletonStrengthLE φ ψ) :
    WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W φ ≤
      WorldModel.queryStrength (State := Multiset (PointedFOL L)) (Query := FOLQuery L) W ψ := by
  have himp : ∀ S : PointedFOL L, folSatisfies S φ → folSatisfies S ψ :=
    (pointwiseImplies_iff_singletonStrengthLE φ ψ).mpr hsing
  exact queryStrength_le_of_pointwise (W := W) (φ := φ) (ψ := ψ) himp

end Mettapedia.Logic.PLNWorldModelFOL
