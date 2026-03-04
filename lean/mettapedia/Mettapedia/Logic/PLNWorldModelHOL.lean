import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.HigherOrder.PredCode.Basic

/-!
# Higher-Order (Predicate-Code) Instance for the WM Calculus

This module instantiates `WorldModel` on a higher-order predicate-code fragment:

- state = multiset of pointed individuals,
- query = predicate code (`PredCode U`),
- evidence = positive/negative support counts from pointwise evaluation.

Singleton states recover crisp 0/1 query strength.
-/

namespace Mettapedia.Logic.PLNWorldModelHOL

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

abbrev HOLQuery (U : Type*) := Mettapedia.Logic.HigherOrder.PredCode U

/-- A pointed HOL state with one individual witness. -/
structure PointedHOL (U : Type*) where
  point : U

/-- Predicate-code satisfaction at a pointed individual. -/
def PointedHOL.satisfies {U : Type*} (pw : PointedHOL U) (q : HOLQuery U) : Prop :=
  Mettapedia.Logic.HigherOrder.evalPred q pw.point

instance {U : Type*} : EvidenceType (Multiset (PointedHOL U)) where

/-- Evidence extracted from a multiset of pointed HOL states:
`pos` counts points satisfying `q`, `neg` counts points refuting `q`. -/
noncomputable def holEvidence {U : Type*}
    (W : Multiset (PointedHOL U)) (q : HOLQuery U) : Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun pw => pw.satisfies q) W : ℝ≥0∞),
     (Multiset.countP (fun pw => ¬ pw.satisfies q) W : ℝ≥0∞)⟩

theorem holEvidence_add {U : Type*}
    (W₁ W₂ : Multiset (PointedHOL U)) (q : HOLQuery U) :
    holEvidence (W₁ + W₂) q = holEvidence W₁ q + holEvidence W₂ q := by
  classical
  apply Evidence.ext'
  · simp [holEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [holEvidence, Multiset.countP_add, Evidence.hplus_def]

/-- Concrete `WorldModel` instance induced by multiset HOL evidence counting. -/
noncomputable instance {U : Type*} : WorldModel (Multiset (PointedHOL U)) (HOLQuery U) where
  evidence := holEvidence
  evidence_add := holEvidence_add

theorem holEvidence_singleton_of_satisfies {U : Type*}
    (pw : PointedHOL U) (q : HOLQuery U) (h : pw.satisfies q) :
    holEvidence ({pw} : Multiset (PointedHOL U)) q = ⟨1, 0⟩ := by
  classical
  ext <;> simp [holEvidence, ← Multiset.cons_zero, h]

theorem holEvidence_singleton_of_not_satisfies {U : Type*}
    (pw : PointedHOL U) (q : HOLQuery U) (h : ¬ pw.satisfies q) :
    holEvidence ({pw} : Multiset (PointedHOL U)) q = ⟨0, 1⟩ := by
  classical
  ext <;> simp [holEvidence, ← Multiset.cons_zero, h]

/-- Singleton WM states recover crisp 0/1 query strength from predicate-code truth. -/
theorem queryStrength_singleton_of_satisfies {U : Type*}
    (pw : PointedHOL U) (q : HOLQuery U) (h : pw.satisfies q) :
    WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
        ({pw} : Multiset (PointedHOL U)) q = 1 := by
  change Evidence.toStrength (holEvidence ({pw} : Multiset (PointedHOL U)) q) = 1
  rw [holEvidence_singleton_of_satisfies pw q h]
  simp [Evidence.toStrength, Evidence.total]

theorem queryStrength_singleton_of_not_satisfies {U : Type*}
    (pw : PointedHOL U) (q : HOLQuery U) (h : ¬ pw.satisfies q) :
    WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
        ({pw} : Multiset (PointedHOL U)) q = 0 := by
  change Evidence.toStrength (holEvidence ({pw} : Multiset (PointedHOL U)) q) = 0
  rw [holEvidence_singleton_of_not_satisfies pw q h]
  simp [Evidence.toStrength, Evidence.total]

/-- Singleton adequacy: predicate-code truth iff WM query strength is `1`. -/
theorem singleton_adequacy_strength_one {U : Type*}
    (pw : PointedHOL U) (q : HOLQuery U) :
    pw.satisfies q ↔
      WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
        ({pw} : Multiset (PointedHOL U)) q = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies pw q h
  · intro h
    by_cases hs : pw.satisfies q
    · exact hs
    · have h0 :
          WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
              ({pw} : Multiset (PointedHOL U)) q = 0 :=
        queryStrength_singleton_of_not_satisfies pw q hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
                ({pw} : Multiset (PointedHOL U)) q := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-! ## Consequence adequacy on singleton and multiset HOL states -/

/-- Singleton-strength consequence schema for HOL WM states. -/
def singletonStrengthLE {U : Type*} (q₁ q₂ : HOLQuery U) : Prop :=
  ∀ pw : PointedHOL U,
    WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
        ({pw} : Multiset (PointedHOL U)) q₁ ≤
      WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
        ({pw} : Multiset (PointedHOL U)) q₂

/-- Pointwise semantic implication is equivalent to singleton-strength consequence. -/
theorem pointwiseImplies_iff_singletonStrengthLE {U : Type*}
    (q₁ q₂ : HOLQuery U) :
    (∀ pw : PointedHOL U, pw.satisfies q₁ → pw.satisfies q₂) ↔
      singletonStrengthLE q₁ q₂ := by
  constructor
  · intro himp pw
    by_cases hq₁ : pw.satisfies q₁
    · have hq₂ : pw.satisfies q₂ := himp pw hq₁
      rw [queryStrength_singleton_of_satisfies pw q₁ hq₁]
      rw [queryStrength_singleton_of_satisfies pw q₂ hq₂]
    · rw [queryStrength_singleton_of_not_satisfies pw q₁ hq₁]
      exact zero_le _
  · intro hle pw hq₁
    by_contra hq₂
    have hsingleton := hle pw
    have h1 :
        WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
            ({pw} : Multiset (PointedHOL U)) q₁ = 1 :=
      queryStrength_singleton_of_satisfies pw q₁ hq₁
    have h0 :
        WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U)
            ({pw} : Multiset (PointedHOL U)) q₂ = 0 :=
      queryStrength_singleton_of_not_satisfies pw q₂ hq₂
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      simp [h1, h0] at htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp {U : Type*}
    (W : Multiset (PointedHOL U))
    {p q : PointedHOL U → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ pw, p pw → q pw) :
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

private theorem holEvidence_total {U : Type*}
    (W : Multiset (PointedHOL U)) (q : HOLQuery U) :
    (holEvidence W q).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pw : PointedHOL U => pw.satisfies q) W +
          Multiset.countP (fun pw : PointedHOL U => ¬ pw.satisfies q) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pw : PointedHOL U => pw.satisfies q) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pw : PointedHOL U => pw.satisfies q) W : ℝ≥0∞) +
          (Multiset.countP (fun pw : PointedHOL U => ¬ pw.satisfies q) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold holEvidence Evidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to WM strength inequality on multiset states. -/
theorem queryStrength_le_of_pointwise {U : Type*}
    (W : Multiset (PointedHOL U)) (q₁ q₂ : HOLQuery U)
    (himp : ∀ pw : PointedHOL U, pw.satisfies q₁ → pw.satisfies q₂) :
    WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U) W q₁ ≤
      WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U) W q₂ := by
  let p₁ : PointedHOL U → Prop := fun pw => pw.satisfies q₁
  let p₂ : PointedHOL U → Prop := fun pw => pw.satisfies q₂
  letI : DecidablePred p₁ := Classical.decPred p₁
  letI : DecidablePred p₂ := Classical.decPred p₂
  have hq₁ :
      WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U) W q₁ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (holEvidence W q₁).total = 0 then 0
      else (holEvidence W q₁).pos / (holEvidence W q₁).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [holEvidence_total (W := W) (q := q₁)]
    simp [holEvidence, p₁]
  have hq₂ :
      WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U) W q₂ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (holEvidence W q₂).total = 0 then 0
      else (holEvidence W q₂).pos / (holEvidence W q₂).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [holEvidence_total (W := W) (q := q₂)]
    simp [holEvidence, p₂]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hq₁, hq₂, hcard]
    simp
  · rw [hq₁, hq₂]
    simp [hcard]
    have hcountNat :
        Multiset.countP p₁ W ≤ Multiset.countP p₂ W :=
      countP_le_countP_of_imp (W := W) (p := p₁) (q := p₂) (by
        intro pw hp
        exact himp pw (by simpa [p₁] using hp))
    have hcount :
        (Multiset.countP p₁ W : ℝ≥0∞) ≤
          (Multiset.countP p₂ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from singleton-strength assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLE {U : Type*}
    (W : Multiset (PointedHOL U)) (q₁ q₂ : HOLQuery U)
    (hsing : singletonStrengthLE q₁ q₂) :
    WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U) W q₁ ≤
      WorldModel.queryStrength (State := Multiset (PointedHOL U)) (Query := HOLQuery U) W q₂ := by
  have himp : ∀ pw : PointedHOL U, pw.satisfies q₁ → pw.satisfies q₂ :=
    (pointwiseImplies_iff_singletonStrengthLE q₁ q₂).mpr hsing
  exact queryStrength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) himp

end Mettapedia.Logic.PLNWorldModelHOL
