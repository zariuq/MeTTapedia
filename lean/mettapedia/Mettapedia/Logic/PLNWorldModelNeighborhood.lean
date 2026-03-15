import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNWorldModelKripke
import Foundation.Modal.Neighborhood.Basic

/-!
# Neighborhood Instance for the WM Calculus

Concrete modal-world instance with:

- state = multiset of pointed neighborhood models,
- query = modal formula (`Formula ℕ`),
- evidence = positive/negative support counts from neighborhood satisfaction.

This module mirrors the Kripke WM consequence schema and provides
explicit parallel lemmas.
-/

namespace Mettapedia.Logic.PLNWorldModelNeighborhood

open LO.Modal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

abbrev ModalQuery := Formula ℕ

/-- A pointed neighborhood model (`M,w`). -/
structure PointedNeighborhood where
  model : Neighborhood.Model
  world : model.World

/-- Pointed-model neighborhood satisfaction predicate. -/
def PointedNeighborhood.satisfies (pn : PointedNeighborhood) (φ : ModalQuery) : Prop :=
  Formula.Neighborhood.Satisfies pn.model pn.world φ

instance : EvidenceType (Multiset PointedNeighborhood) where

/-- Evidence extracted from a multiset of pointed neighborhood models:
`pos` counts points satisfying `φ`, `neg` counts points refuting `φ`. -/
noncomputable def neighborhoodEvidence (W : Multiset PointedNeighborhood) (φ : ModalQuery) :
    Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun pn => pn.satisfies φ) W : ℝ≥0∞),
     (Multiset.countP (fun pn => ¬ pn.satisfies φ) W : ℝ≥0∞)⟩

theorem neighborhoodEvidence_add (W₁ W₂ : Multiset PointedNeighborhood) (φ : ModalQuery) :
    neighborhoodEvidence (W₁ + W₂) φ =
      neighborhoodEvidence W₁ φ + neighborhoodEvidence W₂ φ := by
  classical
  apply Evidence.ext'
  · simp [neighborhoodEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [neighborhoodEvidence, Multiset.countP_add, Evidence.hplus_def]

/-- Concrete `WorldModel` instance induced by multiset neighborhood evidence counting. -/
noncomputable instance : WorldModel (Multiset PointedNeighborhood) ModalQuery where
  evidence := neighborhoodEvidence
  evidence_add := neighborhoodEvidence_add
  evidence_zero q := by
    classical
    simp only [neighborhoodEvidence, Multiset.countP_zero, Nat.cast_zero]; rfl

theorem neighborhoodEvidence_singleton_of_satisfies
    (pn : PointedNeighborhood) (φ : ModalQuery) (h : pn.satisfies φ) :
    neighborhoodEvidence ({pn} : Multiset PointedNeighborhood) φ = ⟨1, 0⟩ := by
  classical
  ext <;> simp [neighborhoodEvidence, ← Multiset.cons_zero, h]

theorem neighborhoodEvidence_singleton_of_not_satisfies
    (pn : PointedNeighborhood) (φ : ModalQuery) (h : ¬ pn.satisfies φ) :
    neighborhoodEvidence ({pn} : Multiset PointedNeighborhood) φ = ⟨0, 1⟩ := by
  classical
  ext <;> simp [neighborhoodEvidence, ← Multiset.cons_zero, h]

/-- Singleton WM states recover crisp 0/1 query strength from pointed neighborhood truth. -/
theorem queryStrength_singleton_of_satisfies
    (pn : PointedNeighborhood) (φ : ModalQuery) (h : pn.satisfies φ) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({pn} : Multiset PointedNeighborhood) φ = 1 := by
  change Evidence.toStrength (neighborhoodEvidence ({pn} : Multiset PointedNeighborhood) φ) = 1
  rw [neighborhoodEvidence_singleton_of_satisfies pn φ h]
  simp [Evidence.toStrength, Evidence.total]

theorem queryStrength_singleton_of_not_satisfies
    (pn : PointedNeighborhood) (φ : ModalQuery) (h : ¬ pn.satisfies φ) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({pn} : Multiset PointedNeighborhood) φ = 0 := by
  change Evidence.toStrength (neighborhoodEvidence ({pn} : Multiset PointedNeighborhood) φ) = 0
  rw [neighborhoodEvidence_singleton_of_not_satisfies pn φ h]
  simp [Evidence.toStrength, Evidence.total]

/-- Singleton adequacy: pointed neighborhood truth iff WM query strength is `1`. -/
theorem singleton_adequacy_strength_one (pn : PointedNeighborhood) (φ : ModalQuery) :
    pn.satisfies φ ↔
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({pn} : Multiset PointedNeighborhood) φ = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies pn φ h
  · intro h
    by_cases hs : pn.satisfies φ
    · exact hs
    · have h0 :
          WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
              ({pn} : Multiset PointedNeighborhood) φ = 0 :=
        queryStrength_singleton_of_not_satisfies pn φ hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
                ({pn} : Multiset PointedNeighborhood) φ := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-! ## Consequence adequacy on singleton and multiset neighborhood states -/

/-- Singleton-strength consequence schema for neighborhood WM states. -/
def singletonStrengthLE (φ ψ : ModalQuery) : Prop :=
  ∀ pn : PointedNeighborhood,
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({pn} : Multiset PointedNeighborhood) φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({pn} : Multiset PointedNeighborhood) ψ

/-- Pointwise semantic implication is equivalent to singleton-strength consequence. -/
theorem pointwiseImplies_iff_singletonStrengthLE (φ ψ : ModalQuery) :
    (∀ pn : PointedNeighborhood, pn.satisfies φ → pn.satisfies ψ) ↔
      singletonStrengthLE φ ψ := by
  constructor
  · intro himp pn
    by_cases hφ : pn.satisfies φ
    · have hψ : pn.satisfies ψ := himp pn hφ
      rw [queryStrength_singleton_of_satisfies pn φ hφ]
      rw [queryStrength_singleton_of_satisfies pn ψ hψ]
    · rw [queryStrength_singleton_of_not_satisfies pn φ hφ]
      exact zero_le _
  · intro hle pn hφ
    by_contra hψ
    have hsingleton := hle pn
    have h1 :
        WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            ({pn} : Multiset PointedNeighborhood) φ = 1 :=
      queryStrength_singleton_of_satisfies pn φ hφ
    have h0 :
        WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            ({pn} : Multiset PointedNeighborhood) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies pn ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      simp [h1, h0] at htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp
    (W : Multiset PointedNeighborhood)
    {p q : PointedNeighborhood → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ pn, p pn → q pn) :
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

private theorem neighborhoodEvidence_total
    (W : Multiset PointedNeighborhood) (φ : ModalQuery) :
    (neighborhoodEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pn : PointedNeighborhood => PointedNeighborhood.satisfies pn φ) W +
          Multiset.countP (fun pn : PointedNeighborhood => ¬ PointedNeighborhood.satisfies pn φ) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pn : PointedNeighborhood => PointedNeighborhood.satisfies pn φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pn : PointedNeighborhood => PointedNeighborhood.satisfies pn φ) W : ℝ≥0∞) +
          (Multiset.countP (fun pn : PointedNeighborhood => ¬ PointedNeighborhood.satisfies pn φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold neighborhoodEvidence Evidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to WM strength inequality on multiset states. -/
theorem queryStrength_le_of_pointwise
    (W : Multiset PointedNeighborhood) (φ ψ : ModalQuery)
    (himp : ∀ pn : PointedNeighborhood, pn.satisfies φ → pn.satisfies ψ) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  let pφ : PointedNeighborhood → Prop := fun pn => PointedNeighborhood.satisfies pn φ
  let pψ : PointedNeighborhood → Prop := fun pn => PointedNeighborhood.satisfies pn ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (neighborhoodEvidence W φ).total = 0 then 0
      else (neighborhoodEvidence W φ).pos / (neighborhoodEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [neighborhoodEvidence_total (W := W) (φ := φ)]
    simp [neighborhoodEvidence, pφ]
  have hψ :
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (neighborhoodEvidence W ψ).total = 0 then 0
      else (neighborhoodEvidence W ψ).pos / (neighborhoodEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [neighborhoodEvidence_total (W := W) (φ := ψ)]
    simp [neighborhoodEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp (W := W) (p := pφ) (q := pψ) (by
        intro pn hp
        exact himp pn (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from singleton-strength assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLE
    (W : Multiset PointedNeighborhood) (φ ψ : ModalQuery)
    (hsing : singletonStrengthLE φ ψ) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) W ψ := by
  have himp : ∀ pn : PointedNeighborhood, pn.satisfies φ → pn.satisfies ψ :=
    (pointwiseImplies_iff_singletonStrengthLE φ ψ).mpr hsing
  exact queryStrength_le_of_pointwise (W := W) (φ := φ) (ψ := ψ) himp

/-! ## Comparison with Kripke WM consequence behavior -/

abbrev KPointedKripke := Mettapedia.Logic.PLNWorldModelKripke.PointedKripke

/-- Neighborhood and Kripke singleton consequence schemas have the same shape. -/
theorem singleton_consequence_schema_parallel (φ ψ : ModalQuery) :
    ((∀ pn : PointedNeighborhood, pn.satisfies φ → pn.satisfies ψ) ↔ singletonStrengthLE φ ψ) ∧
      ((∀ pk : KPointedKripke, pk.satisfies φ → pk.satisfies ψ) ↔
        Mettapedia.Logic.PLNWorldModelKripke.singletonStrengthLE φ ψ) := by
  exact ⟨pointwiseImplies_iff_singletonStrengthLE φ ψ,
    Mettapedia.Logic.PLNWorldModelKripke.pointwiseImplies_iff_singletonStrengthLE φ ψ⟩

/-- Neighborhood and Kripke multiset lifts both follow singleton-strength assumptions. -/
theorem multiset_lift_schema_parallel (φ ψ : ModalQuery) :
    (∀ Wn : Multiset PointedNeighborhood,
      singletonStrengthLE φ ψ →
        WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) Wn φ ≤
          WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery) Wn ψ) ∧
      (∀ Wk : Multiset KPointedKripke,
      Mettapedia.Logic.PLNWorldModelKripke.singletonStrengthLE φ ψ →
        WorldModel.queryStrength (State := Multiset KPointedKripke) (Query := ModalQuery) Wk φ ≤
          WorldModel.queryStrength (State := Multiset KPointedKripke) (Query := ModalQuery) Wk ψ) := by
  refine ⟨?_, ?_⟩
  · intro Wn hsing
    exact multiset_strength_le_of_singletonStrengthLE (W := Wn) (φ := φ) (ψ := ψ) hsing
  · intro Wk hsing
    exact Mettapedia.Logic.PLNWorldModelKripke.multiset_strength_le_of_singletonStrengthLE
      (W := Wk) (φ := φ) (ψ := ψ) hsing

end Mettapedia.Logic.PLNWorldModelNeighborhood
