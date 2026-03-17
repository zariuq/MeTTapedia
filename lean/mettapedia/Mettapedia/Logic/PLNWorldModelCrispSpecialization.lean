import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# Generic Crisp Specialization Layer for the WM Calculus

This module factors out the shared theorem spine used by several world-model
bridges whose evidence is obtained by counting satisfiers vs refuters of a
crisp semantic relation

`satisfies : Point -> Query -> Prop`.

The current concrete instances using this pattern include:

- first-order sentence satisfaction over pointed structures,
- direct HOL satisfaction over pointed set structures,
- finite predicate-code evaluation over pointed witnesses.

The point of this layer is not to collapse graded/fuzzy semantics into a
crisp interface.  It only captures the common count-based theorem family for
crisp `Prop`-valued satisfaction.
-/

namespace Mettapedia.Logic.PLNWorldModelCrispSpecialization

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe u v

variable {Point : Type u} {Query : Type v}

/-- Generic count-based evidence extracted from a multiset of points and a
crisp satisfaction predicate. -/
noncomputable def crispEvidence
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q : Query) : BinaryEvidence := by
  classical
  exact
    ⟨(Multiset.countP (fun x => satisfies x q) W : ℝ≥0∞),
     (Multiset.countP (fun x => ¬ satisfies x q) W : ℝ≥0∞)⟩

/-- Generic strength view induced by `crispEvidence`. -/
noncomputable def crispQueryStrength
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q : Query) : ℝ≥0∞ :=
  BinaryEvidence.toStrength (crispEvidence satisfies W q)

/-- Singleton-strength consequence schema for a crisp specialization. -/
def singletonStrengthLE
    (satisfies : Point → Query → Prop)
    (q₁ q₂ : Query) : Prop :=
  ∀ x : Point,
    crispQueryStrength satisfies ({x} : Multiset Point) q₁ ≤
      crispQueryStrength satisfies ({x} : Multiset Point) q₂

/-- BinaryEvidence-level query equivalence for a crisp specialization. -/
def CrispQueryEq
    (satisfies : Point → Query → Prop)
    (q₁ q₂ : Query) : Prop :=
  ∀ W : Multiset Point, crispEvidence satisfies W q₁ = crispEvidence satisfies W q₂

theorem crispEvidence_add
    (satisfies : Point → Query → Prop)
    (W₁ W₂ : Multiset Point) (q : Query) :
    crispEvidence satisfies (W₁ + W₂) q =
      crispEvidence satisfies W₁ q + crispEvidence satisfies W₂ q := by
  classical
  apply BinaryEvidence.ext'
  · simp [crispEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]
  · simp [crispEvidence, Multiset.countP_add, BinaryEvidence.hplus_def]

theorem crispEvidence_singleton_of_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : satisfies x q) :
    crispEvidence satisfies ({x} : Multiset Point) q = ⟨1, 0⟩ := by
  classical
  ext <;> simp [crispEvidence, ← Multiset.cons_zero, h]

theorem crispEvidence_singleton_of_not_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : ¬ satisfies x q) :
    crispEvidence satisfies ({x} : Multiset Point) q = ⟨0, 1⟩ := by
  classical
  ext <;> simp [crispEvidence, ← Multiset.cons_zero, h]

/-- Singleton states recover crisp strength `1` from truth. -/
theorem queryStrength_singleton_of_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : satisfies x q) :
    crispQueryStrength satisfies ({x} : Multiset Point) q = 1 := by
  unfold crispQueryStrength
  rw [crispEvidence_singleton_of_satisfies satisfies x q h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

/-- Singleton states recover crisp strength `0` from refutation. -/
theorem queryStrength_singleton_of_not_satisfies
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) (h : ¬ satisfies x q) :
    crispQueryStrength satisfies ({x} : Multiset Point) q = 0 := by
  unfold crispQueryStrength
  rw [crispEvidence_singleton_of_not_satisfies satisfies x q h]
  simp [BinaryEvidence.toStrength, BinaryEvidence.total]

/-- Singleton adequacy: truth iff singleton strength is `1`. -/
theorem singleton_adequacy_strength_one
    (satisfies : Point → Query → Prop)
    (x : Point) (q : Query) :
    satisfies x q ↔ crispQueryStrength satisfies ({x} : Multiset Point) q = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies satisfies x q h
  · intro h
    by_cases hs : satisfies x q
    · exact hs
    · have h0 :
        crispQueryStrength satisfies ({x} : Multiset Point) q = 0 :=
          queryStrength_singleton_of_not_satisfies satisfies x q hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) = crispQueryStrength satisfies ({x} : Multiset Point) q := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

/-- Pointwise semantic implication is equivalent to singleton-strength
consequence for the induced crisp WM view. -/
theorem pointwiseImplies_iff_singletonStrengthLE
    (satisfies : Point → Query → Prop)
    (q₁ q₂ : Query) :
    (∀ x : Point, satisfies x q₁ → satisfies x q₂) ↔
      singletonStrengthLE satisfies q₁ q₂ := by
  constructor
  · intro himp x
    by_cases hq₁ : satisfies x q₁
    · have hq₂ : satisfies x q₂ := himp x hq₁
      rw [queryStrength_singleton_of_satisfies satisfies x q₁ hq₁]
      rw [queryStrength_singleton_of_satisfies satisfies x q₂ hq₂]
    · rw [queryStrength_singleton_of_not_satisfies satisfies x q₁ hq₁]
      exact zero_le _
  · intro hle x hq₁
    by_contra hq₂
    have hsingleton := hle x
    have h1 :
        crispQueryStrength satisfies ({x} : Multiset Point) q₁ = 1 :=
      queryStrength_singleton_of_satisfies satisfies x q₁ hq₁
    have h0 :
        crispQueryStrength satisfies ({x} : Multiset Point) q₂ = 0 :=
      queryStrength_singleton_of_not_satisfies satisfies x q₂ hq₂
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      rw [h1, h0] at hsingleton
      exact hsingleton
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp
    (W : Multiset Point)
    {p q : Point → Prop}
    [DecidablePred p] [DecidablePred q]
    (himp : ∀ x, p x → q x) :
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

private theorem crispEvidence_total
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q : Query) :
    (crispEvidence satisfies W q).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun x : Point => satisfies x q) W +
          Multiset.countP (fun x : Point => ¬ satisfies x q) W := by
    simpa using
      (Multiset.card_eq_countP_add_countP (p := fun x : Point => satisfies x q) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun x : Point => satisfies x q) W : ℝ≥0∞) +
          (Multiset.countP (fun x : Point => ¬ satisfies x q) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold crispEvidence BinaryEvidence.total
  simpa using hcard.symm

/-- Pointwise semantic implication lifts to multiset strength inequality. -/
theorem queryStrength_le_of_pointwise
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (himp : ∀ x : Point, satisfies x q₁ → satisfies x q₂) :
    crispQueryStrength satisfies W q₁ ≤ crispQueryStrength satisfies W q₂ := by
  let p₁ : Point → Prop := fun x => satisfies x q₁
  let p₂ : Point → Prop := fun x => satisfies x q₂
  letI : DecidablePred p₁ := Classical.decPred p₁
  letI : DecidablePred p₂ := Classical.decPred p₂
  have hq₁ :
      crispQueryStrength satisfies W q₁ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold crispQueryStrength BinaryEvidence.toStrength
    rw [crispEvidence_total satisfies (W := W) (q := q₁)]
    simp [crispEvidence, p₁]
  have hq₂ :
      crispQueryStrength satisfies W q₂ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold crispQueryStrength BinaryEvidence.toStrength
    rw [crispEvidence_total satisfies (W := W) (q := q₂)]
    simp [crispEvidence, p₂]
  by_cases hcard : (W.card : ℝ≥0∞) = 0
  · rw [hq₁, hq₂, hcard]
    simp
  · rw [hq₁, hq₂]
    simp [hcard]
    have hcountNat :
        Multiset.countP p₁ W ≤ Multiset.countP p₂ W :=
      countP_le_countP_of_imp (W := W) (p := p₁) (q := p₂) (by
        intro x hx
        exact himp x (by simpa [p₁] using hx))
    have hcount :
        (Multiset.countP p₁ W : ℝ≥0∞) ≤
          (Multiset.countP p₂ W : ℝ≥0∞) := by
      exact_mod_cast hcountNat
    exact ENNReal.div_le_div_right hcount (W.card : ℝ≥0∞)

/-- Multiset consequence lifting from singleton-strength assumptions. -/
theorem multiset_strength_le_of_singletonStrengthLE
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (hsing : singletonStrengthLE satisfies q₁ q₂) :
    crispQueryStrength satisfies W q₁ ≤ crispQueryStrength satisfies W q₂ := by
  have himp : ∀ x : Point, satisfies x q₁ → satisfies x q₂ :=
    (pointwiseImplies_iff_singletonStrengthLE satisfies q₁ q₂).mpr hsing
  exact queryStrength_le_of_pointwise satisfies W q₁ q₂ himp

/-- Pointwise semantic equivalence yields evidence-level query equivalence. -/
theorem queryEq_of_pointwiseIff
    (satisfies : Point → Query → Prop)
    (q₁ q₂ : Query)
    (hiff : ∀ x : Point, satisfies x q₁ ↔ satisfies x q₂) :
    CrispQueryEq satisfies q₁ q₂ := by
  intro W
  classical
  ext <;> simp [crispEvidence, hiff]

/-- BinaryEvidence-level query equivalence transports crisp query strength. -/
theorem queryEq_to_queryStrength
    (satisfies : Point → Query → Prop)
    {q₁ q₂ : Query}
    (hEq : CrispQueryEq satisfies q₁ q₂)
    (W : Multiset Point) :
    crispQueryStrength satisfies W q₁ = crispQueryStrength satisfies W q₂ := by
  unfold crispQueryStrength
  simpa using congrArg BinaryEvidence.toStrength (hEq W)

/-- Pointwise semantic equivalence yields equality of multiset strengths. -/
theorem queryStrength_eq_of_pointwiseIff
    (satisfies : Point → Query → Prop)
    (W : Multiset Point) (q₁ q₂ : Query)
    (hiff : ∀ x : Point, satisfies x q₁ ↔ satisfies x q₂) :
    crispQueryStrength satisfies W q₁ = crispQueryStrength satisfies W q₂ := by
  exact queryEq_to_queryStrength satisfies (queryEq_of_pointwiseIff satisfies q₁ q₂ hiff) W

/-- Pointwise semantic equivalence is exactly evidence-level query equivalence
for crisp specializations. -/
theorem pointwiseIff_iff_queryEq
    (satisfies : Point → Query → Prop)
    (q₁ q₂ : Query) :
    (∀ x : Point, satisfies x q₁ ↔ satisfies x q₂) ↔
      CrispQueryEq satisfies q₁ q₂ := by
  constructor
  · intro hiff
    exact queryEq_of_pointwiseIff satisfies q₁ q₂ hiff
  · intro hEq x
    constructor
    · intro hq₁
      have hStrength :=
        queryEq_to_queryStrength satisfies hEq ({x} : Multiset Point)
      have hleft :
          crispQueryStrength satisfies ({x} : Multiset Point) q₁ = 1 :=
        queryStrength_singleton_of_satisfies satisfies x q₁ hq₁
      rw [hleft] at hStrength
      exact (singleton_adequacy_strength_one satisfies x q₂).2 hStrength.symm
    · intro hq₂
      have hStrength :=
        queryEq_to_queryStrength satisfies hEq ({x} : Multiset Point)
      have hright :
          crispQueryStrength satisfies ({x} : Multiset Point) q₂ = 1 :=
        queryStrength_singleton_of_satisfies satisfies x q₂ hq₂
      rw [hright] at hStrength
      exact (singleton_adequacy_strength_one satisfies x q₁).2 hStrength

end Mettapedia.Logic.PLNWorldModelCrispSpecialization
