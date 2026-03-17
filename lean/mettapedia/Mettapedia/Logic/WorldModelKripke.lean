import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModel
import Foundation.Modal.Kripke.Basic

/-!
# Kripke Instance for the WM Calculus

This module gives a concrete modal-world instance of `BinaryWorldModel`:

- state = multiset of pointed Kripke models (provenance with multiplicity),
- query = modal formula (`Formula ℕ`),
- evidence = positive/negative support counts from pointwise satisfaction.

The core adequacy theorem shows singleton states recover ordinary pointed-model
truth as a WM query-strength equation.
-/

namespace Mettapedia.Logic.PLNWorldModelKripke

open LO.Modal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

abbrev ModalQuery := Formula ℕ

/-- A pointed Kripke model (`M,w`). -/
structure PointedKripke where
  model : Kripke.Model
  world : model.World

/-- Pointed-model satisfaction predicate. -/
def PointedKripke.satisfies (pk : PointedKripke) (φ : ModalQuery) : Prop :=
  Formula.Kripke.Satisfies pk.model pk.world φ

instance : EvidenceType (Multiset PointedKripke) where

/-- BinaryEvidence extracted from a multiset of pointed models:
`pos` counts points satisfying `φ`, `neg` counts points refuting `φ`. -/
noncomputable def kripkeEvidence (W : Multiset PointedKripke) (φ : ModalQuery) : BinaryEvidence := by
  classical
  exact
    ⟨(Multiset.countP (fun pk => pk.satisfies φ) W : ℝ≥0∞),
     (Multiset.countP (fun pk => ¬ pk.satisfies φ) W : ℝ≥0∞)⟩

theorem kripkeEvidence_add (W₁ W₂ : Multiset PointedKripke) (φ : ModalQuery) :
    kripkeEvidence (W₁ + W₂) φ = kripkeEvidence W₁ φ + kripkeEvidence W₂ φ := by
  classical
  apply BinaryEvidence.ext'
  · simp [kripkeEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]
  · simp [kripkeEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

/-- Concrete `BinaryWorldModel` instance induced by multiset Kripke evidence counting. -/
noncomputable instance : BinaryWorldModel (Multiset PointedKripke) ModalQuery where
  evidence := kripkeEvidence
  evidence_add := kripkeEvidence_add
  evidence_zero q := by
    classical
    simp only [kripkeEvidence, Multiset.countP_zero, Nat.cast_zero]; rfl

theorem kripkeEvidence_singleton_of_satisfies
    (pk : PointedKripke) (φ : ModalQuery) (h : pk.satisfies φ) :
    kripkeEvidence ({pk} : Multiset PointedKripke) φ = ⟨1, 0⟩ := by
  classical
  ext <;> simp [kripkeEvidence, ← Multiset.cons_zero, h]

theorem kripkeEvidence_singleton_of_not_satisfies
    (pk : PointedKripke) (φ : ModalQuery) (h : ¬ pk.satisfies φ) :
    kripkeEvidence ({pk} : Multiset PointedKripke) φ = ⟨0, 1⟩ := by
  classical
  ext <;> simp [kripkeEvidence, ← Multiset.cons_zero, h]

/-- Singleton WM states recover crisp 0/1 query strength from pointed-model truth. -/
theorem queryStrength_singleton_of_satisfies
    (pk : PointedKripke) (φ : ModalQuery) (h : pk.satisfies φ) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        ({pk} : Multiset PointedKripke) φ = 1 := by
  change BinaryEvidence.toStrength (kripkeEvidence ({pk} : Multiset PointedKripke) φ) = 1
  rw [kripkeEvidence_singleton_of_satisfies pk φ h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

theorem queryStrength_singleton_of_not_satisfies
    (pk : PointedKripke) (φ : ModalQuery) (h : ¬ pk.satisfies φ) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        ({pk} : Multiset PointedKripke) φ = 0 := by
  change BinaryEvidence.toStrength (kripkeEvidence ({pk} : Multiset PointedKripke) φ) = 0
  rw [kripkeEvidence_singleton_of_not_satisfies pk φ h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

/-- Singleton adequacy: pointed-model truth iff WM query strength is `1`. -/
theorem singleton_adequacy_strength_one (pk : PointedKripke) (φ : ModalQuery) :
    pk.satisfies φ ↔
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        ({pk} : Multiset PointedKripke) φ = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies pk φ h
  · intro h
    by_cases hs : pk.satisfies φ
    · exact hs
    · have h0 :
          BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
              ({pk} : Multiset PointedKripke) φ = 0 :=
        queryStrength_singleton_of_not_satisfies pk φ hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
                ({pk} : Multiset PointedKripke) φ := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-! ## Consequence adequacy on singleton and multiset Kripke states -/

/-- Singleton-strength consequence schema for Kripke WM states. -/
def singletonStrengthLE (φ ψ : ModalQuery) : Prop :=
  ∀ pk : PointedKripke,
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        ({pk} : Multiset PointedKripke) φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        ({pk} : Multiset PointedKripke) ψ

/-- Pointwise semantic implication is equivalent to singleton-strength consequence. -/
theorem pointwiseImplies_iff_singletonStrengthLE (φ ψ : ModalQuery) :
    (∀ pk : PointedKripke, pk.satisfies φ → pk.satisfies ψ) ↔
      singletonStrengthLE φ ψ := by
  constructor
  · intro himp pk
    by_cases hφ : pk.satisfies φ
    · have hψ : pk.satisfies ψ := himp pk hφ
      rw [queryStrength_singleton_of_satisfies pk φ hφ]
      rw [queryStrength_singleton_of_satisfies pk ψ hψ]
    · rw [queryStrength_singleton_of_not_satisfies pk φ hφ]
      exact zero_le _
  · intro hle pk hφ
    by_contra hψ
    have hsingleton := hle pk
    have h1 :
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
            ({pk} : Multiset PointedKripke) φ = 1 :=
      queryStrength_singleton_of_satisfies pk φ hφ
    have h0 :
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
            ({pk} : Multiset PointedKripke) ψ = 0 :=
      queryStrength_singleton_of_not_satisfies pk ψ hψ
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      simp [h1, h0] at htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp
    (W : Multiset PointedKripke)
    {p q : PointedKripke → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ pk, p pk → q pk) :
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

private theorem kripkeEvidence_total
    (W : Multiset PointedKripke) (φ : ModalQuery) :
    (kripkeEvidence W φ).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pk : PointedKripke => PointedKripke.satisfies pk φ) W +
          Multiset.countP (fun pk : PointedKripke => ¬ PointedKripke.satisfies pk φ) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pk : PointedKripke => PointedKripke.satisfies pk φ) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pk : PointedKripke => PointedKripke.satisfies pk φ) W : ℝ≥0∞) +
          (Multiset.countP (fun pk : PointedKripke => ¬ PointedKripke.satisfies pk φ) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold kripkeEvidence BinaryEvidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to WM strength inequality on multiset states. -/
theorem queryStrength_le_of_pointwise
    (W : Multiset PointedKripke) (φ ψ : ModalQuery)
    (himp : ∀ pk : PointedKripke, pk.satisfies φ → pk.satisfies ψ) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  let pφ : PointedKripke → Prop := fun pk => PointedKripke.satisfies pk φ
  let pψ : PointedKripke → Prop := fun pk => PointedKripke.satisfies pk ψ
  letI : DecidablePred pφ := Classical.decPred pφ
  letI : DecidablePred pψ := Classical.decPred pψ
  have hφ :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
    change (if (kripkeEvidence W φ).total = 0 then 0
      else (kripkeEvidence W φ).pos / (kripkeEvidence W φ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pφ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [kripkeEvidence_total (W := W) (φ := φ)]
    simp [kripkeEvidence, pφ]
  have hψ :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold BinaryWorldModel.queryStrength BinaryEvidence.toStrength
    change (if (kripkeEvidence W ψ).total = 0 then 0
      else (kripkeEvidence W ψ).pos / (kripkeEvidence W ψ).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP pψ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [kripkeEvidence_total (W := W) (φ := ψ)]
    simp [kripkeEvidence, pψ]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hφ, hψ, hcard]
    simp
  · rw [hφ, hψ]
    simp [hcard]
    have hcountNat :
        Multiset.countP pφ W ≤ Multiset.countP pψ W :=
      countP_le_countP_of_imp (W := W) (p := pφ) (q := pψ) (by
        intro pk hp
        exact himp pk (by simpa [pφ] using hp))
    have hcount :
        (Multiset.countP pφ W : ℝ≥0∞) ≤
          (Multiset.countP pψ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from singleton-strength assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLE
    (W : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hsing : singletonStrengthLE φ ψ) :
    BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery) W ψ := by
  have himp : ∀ pk : PointedKripke, pk.satisfies φ → pk.satisfies ψ :=
    (pointwiseImplies_iff_singletonStrengthLE φ ψ).mpr hsing
  exact queryStrength_le_of_pointwise (W := W) (φ := φ) (ψ := ψ) himp

end Mettapedia.Logic.PLNWorldModelKripke
