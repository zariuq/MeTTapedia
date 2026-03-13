import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelCrispSpecialization
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.HigherOrder.PredCode.Basic

/-!
# Predicate-Code Instance for the WM Calculus

This module preserves the older predicate-code world-model bridge under an
honest public name:

- state = multiset of pointed individuals,
- query = finite Boolean predicate code,
- evidence = positive/negative support counts from pointwise evaluation.

This is a useful fragment, but it is not the general Church/Henkin HOL layer.
-/

namespace Mettapedia.Logic.PLNWorldModelPredCode

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-- Predicate-code query type. -/
abbrev PredCodeQuery (U : Type*) := Mettapedia.Logic.HigherOrder.PredCode U

/-- A pointed predicate-code state with one individual witness. -/
structure PointedPredCode (U : Type*) where
  point : U

/-- Predicate-code satisfaction at a pointed individual. -/
def PointedPredCode.satisfies {U : Type*} (pw : PointedPredCode U) (q : PredCodeQuery U) : Prop :=
  Mettapedia.Logic.HigherOrder.evalPred q pw.point

/-- Predicate-code world-model states are multisets of pointed witnesses. -/
abbrev PredCodeState (U : Type*) := Multiset (PointedPredCode U)

instance {U : Type*} : EvidenceType (PredCodeState U) where

/-- Evidence extracted from a multiset of pointed predicate-code states:
`pos` counts points satisfying `q`, `neg` counts points refuting `q`. -/
noncomputable def predCodeEvidence {U : Type*}
    (W : PredCodeState U) (q : PredCodeQuery U) : Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun pw => pw.satisfies q) W : ℝ≥0∞),
     (Multiset.countP (fun pw => ¬ pw.satisfies q) W : ℝ≥0∞)⟩

/-- The predicate-code bridge is a direct instance of the generic
crisp-specialization evidence extractor. -/
theorem predCodeEvidence_eq_crispEvidence {U : Type*}
    (W : PredCodeState U) (q : PredCodeQuery U) :
    predCodeEvidence W q =
      Mettapedia.Logic.PLNWorldModelCrispSpecialization.crispEvidence
        PointedPredCode.satisfies W q := by
  rfl

theorem predCodeEvidence_add {U : Type*}
    (W₁ W₂ : PredCodeState U) (q : PredCodeQuery U) :
    predCodeEvidence (W₁ + W₂) q = predCodeEvidence W₁ q + predCodeEvidence W₂ q := by
  classical
  apply Evidence.ext'
  · simp [predCodeEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [predCodeEvidence, Multiset.countP_add, Evidence.hplus_def]

/-- Concrete `WorldModel` instance induced by multiset predicate-code evidence counting. -/
noncomputable instance {U : Type*} : WorldModel (PredCodeState U) (PredCodeQuery U) where
  evidence := predCodeEvidence
  evidence_add := predCodeEvidence_add

theorem predCodeEvidence_singleton_of_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeQuery U) (h : pw.satisfies q) :
    predCodeEvidence ({pw} : PredCodeState U) q = ⟨1, 0⟩ := by
  classical
  ext <;> simp [predCodeEvidence, ← Multiset.cons_zero, h]

theorem predCodeEvidence_singleton_of_not_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeQuery U) (h : ¬ pw.satisfies q) :
    predCodeEvidence ({pw} : PredCodeState U) q = ⟨0, 1⟩ := by
  classical
  ext <;> simp [predCodeEvidence, ← Multiset.cons_zero, h]

/-- Singleton WM states recover crisp 0/1 query strength from predicate-code truth. -/
theorem queryStrength_singleton_of_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeQuery U) (h : pw.satisfies q) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
        ({pw} : PredCodeState U) q = 1 := by
  change Evidence.toStrength (predCodeEvidence ({pw} : PredCodeState U) q) = 1
  rw [predCodeEvidence_singleton_of_satisfies pw q h]
  simp [Evidence.toStrength, Evidence.total]

theorem queryStrength_singleton_of_not_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeQuery U) (h : ¬ pw.satisfies q) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
        ({pw} : PredCodeState U) q = 0 := by
  change Evidence.toStrength (predCodeEvidence ({pw} : PredCodeState U) q) = 0
  rw [predCodeEvidence_singleton_of_not_satisfies pw q h]
  simp [Evidence.toStrength, Evidence.total]

/-- Singleton adequacy: predicate-code truth iff WM query strength is `1`. -/
theorem singleton_adequacy_strength_one {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeQuery U) :
    pw.satisfies q ↔
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
        ({pw} : PredCodeState U) q = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies pw q h
  · intro h
    by_cases hs : pw.satisfies q
    · exact hs
    · have h0 :
          WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
              ({pw} : PredCodeState U) q = 0 :=
        queryStrength_singleton_of_not_satisfies pw q hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
                ({pw} : PredCodeState U) q := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-- Explicit witness that the singleton adequacy theorem for predicate-code is
an instance of the generic crisp-specialization theorem family. -/
theorem singleton_adequacy_strength_one_is_crispSpecialization {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeQuery U) :
    pw.satisfies q ↔
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
        ({pw} : PredCodeState U) q = 1 := by
  simpa [Mettapedia.Logic.PLNWorldModelCrispSpecialization.crispQueryStrength,
    WorldModel.queryStrength, predCodeEvidence_eq_crispEvidence]
    using
      (Mettapedia.Logic.PLNWorldModelCrispSpecialization.singleton_adequacy_strength_one
        (satisfies := PointedPredCode.satisfies) pw q)

/-! ## Consequence adequacy on singleton and multiset predicate-code states -/

/-- Singleton-strength consequence schema for predicate-code WM states. -/
def singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeQuery U) : Prop :=
  ∀ pw : PointedPredCode U,
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
        ({pw} : PredCodeState U) q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
        ({pw} : PredCodeState U) q₂

/-- Pointwise semantic implication is equivalent to singleton-strength consequence. -/
theorem pointwiseImplies_iff_singletonStrengthLE {U : Type*}
    (q₁ q₂ : PredCodeQuery U) :
    (∀ pw : PointedPredCode U, pw.satisfies q₁ → pw.satisfies q₂) ↔
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
        WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
            ({pw} : PredCodeState U) q₁ = 1 :=
      queryStrength_singleton_of_satisfies pw q₁ hq₁
    have h0 :
        WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U)
            ({pw} : PredCodeState U) q₂ = 0 :=
      queryStrength_singleton_of_not_satisfies pw q₂ hq₂
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      simp [h1, h0] at htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp {U : Type*}
    (W : PredCodeState U)
    {p q : PointedPredCode U → Prop}
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

private theorem predCodeEvidence_total {U : Type*}
    (W : PredCodeState U) (q : PredCodeQuery U) :
    (predCodeEvidence W q).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pw : PointedPredCode U => pw.satisfies q) W +
          Multiset.countP (fun pw : PointedPredCode U => ¬ pw.satisfies q) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pw : PointedPredCode U => pw.satisfies q) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pw : PointedPredCode U => pw.satisfies q) W : ℝ≥0∞) +
          (Multiset.countP (fun pw : PointedPredCode U => ¬ pw.satisfies q) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold predCodeEvidence Evidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to WM strength inequality on multiset states. -/
theorem queryStrength_le_of_pointwise {U : Type*}
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (himp : ∀ pw : PointedPredCode U, pw.satisfies q₁ → pw.satisfies q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ := by
  let p₁ : PointedPredCode U → Prop := fun pw => pw.satisfies q₁
  let p₂ : PointedPredCode U → Prop := fun pw => pw.satisfies q₂
  letI : DecidablePred p₁ := Classical.decPred p₁
  letI : DecidablePred p₂ := Classical.decPred p₂
  have hq₁ :
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (predCodeEvidence W q₁).total = 0 then 0
      else (predCodeEvidence W q₁).pos / (predCodeEvidence W q₁).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [predCodeEvidence_total (W := W) (q := q₁)]
    simp [predCodeEvidence, p₁]
  have hq₂ :
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (predCodeEvidence W q₂).total = 0 then 0
      else (predCodeEvidence W q₂).pos / (predCodeEvidence W q₂).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [predCodeEvidence_total (W := W) (q := q₂)]
    simp [predCodeEvidence, p₂]
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
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (hsing : singletonStrengthLE q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ := by
  have himp : ∀ pw : PointedPredCode U, pw.satisfies q₁ → pw.satisfies q₂ :=
    (pointwiseImplies_iff_singletonStrengthLE q₁ q₂).mpr hsing
  exact queryStrength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) himp

end Mettapedia.Logic.PLNWorldModelPredCode
