import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Count
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelPredCode

/-!
# Infinitary Predicate-Code Instance for WM Calculus

This preserves the older countably infinitary query fragment built on top of the
predicate-code bridge:

- base predicate-code atoms,
- countable conjunctions,
- countable disjunctions.

It is intentionally separate from the real Church-style HOL layer.
-/

namespace Mettapedia.Logic.PLNWorldModelPredCodeInfinitary

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelPredCode
open scoped ENNReal

abbrev BasePredCodeQuery (U : Type*) := Mettapedia.Logic.PLNWorldModelPredCode.PredCodeQuery U
abbrev PointedPredCode (U : Type*) := Mettapedia.Logic.PLNWorldModelPredCode.PointedPredCode U

/-- Countably infinitary predicate-code query fragment. -/
inductive PredCodeInfQuery (U : Type*) where
  | atom : BasePredCodeQuery U → PredCodeInfQuery U
  | iAnd : (Nat → PredCodeInfQuery U) → PredCodeInfQuery U
  | iOr : (Nat → PredCodeInfQuery U) → PredCodeInfQuery U

/-- Relational satisfaction for infinitary predicate-code queries. -/
inductive SatisfiesInf {U : Type*} : PointedPredCode U → PredCodeInfQuery U → Prop where
  | atom {pw : PointedPredCode U} {q : BasePredCodeQuery U} :
      pw.satisfies q → SatisfiesInf pw (.atom q)
  | iAnd {pw : PointedPredCode U} {F : Nat → PredCodeInfQuery U} :
      (∀ n, SatisfiesInf pw (F n)) → SatisfiesInf pw (.iAnd F)
  | iOr {pw : PointedPredCode U} {F : Nat → PredCodeInfQuery U} {n : Nat} :
      SatisfiesInf pw (F n) → SatisfiesInf pw (.iOr F)

theorem satisfiesInf_iAnd_iff {U : Type*}
    (pw : PointedPredCode U) (F : Nat → PredCodeInfQuery U) :
    SatisfiesInf pw (.iAnd F) ↔ ∀ n, SatisfiesInf pw (F n) := by
  constructor
  · intro h
    cases h with
    | iAnd hall => exact hall
  · intro hall
    exact SatisfiesInf.iAnd hall

theorem satisfiesInf_iOr_iff {U : Type*}
    (pw : PointedPredCode U) (F : Nat → PredCodeInfQuery U) :
    SatisfiesInf pw (.iOr F) ↔ ∃ n, SatisfiesInf pw (F n) := by
  constructor
  · intro h
    cases h with
    | iOr hs => exact ⟨_, hs⟩
  · intro h
    rcases h with ⟨n, hn⟩
    exact SatisfiesInf.iOr hn

abbrev PredCodeInfState (U : Type*) := Multiset (PointedPredCode U)

instance {U : Type*} : EvidenceType (PredCodeInfState U) where

/-- Evidence extraction for infinitary predicate-code queries by support/refutation counts. -/
noncomputable def predCodeInfEvidence {U : Type*}
    (W : PredCodeInfState U) (q : PredCodeInfQuery U) : Evidence := by
  classical
  exact
    ⟨(Multiset.countP (fun pw => SatisfiesInf pw q) W : ℝ≥0∞),
     (Multiset.countP (fun pw => ¬ SatisfiesInf pw q) W : ℝ≥0∞)⟩

theorem predCodeInfEvidence_add {U : Type*}
    (W₁ W₂ : PredCodeInfState U) (q : PredCodeInfQuery U) :
    predCodeInfEvidence (W₁ + W₂) q = predCodeInfEvidence W₁ q + predCodeInfEvidence W₂ q := by
  classical
  apply Evidence.ext'
  · simp [predCodeInfEvidence, Multiset.countP_add, Evidence.hplus_def]
  · simp [predCodeInfEvidence, Multiset.countP_add, Evidence.hplus_def]

noncomputable instance {U : Type*} : WorldModel (PredCodeInfState U) (PredCodeInfQuery U) where
  evidence := predCodeInfEvidence
  evidence_add := predCodeInfEvidence_add

theorem predCodeInfEvidence_singleton_of_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeInfQuery U) (h : SatisfiesInf pw q) :
    predCodeInfEvidence ({pw} : PredCodeInfState U) q = ⟨1, 0⟩ := by
  classical
  ext <;> simp [predCodeInfEvidence, ← Multiset.cons_zero, h]

theorem predCodeInfEvidence_singleton_of_not_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeInfQuery U) (h : ¬ SatisfiesInf pw q) :
    predCodeInfEvidence ({pw} : PredCodeInfState U) q = ⟨0, 1⟩ := by
  classical
  ext <;> simp [predCodeInfEvidence, ← Multiset.cons_zero, h]

theorem queryStrength_singleton_of_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeInfQuery U) (h : SatisfiesInf pw q) :
    WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
        ({pw} : PredCodeInfState U) q = 1 := by
  change Evidence.toStrength (predCodeInfEvidence ({pw} : PredCodeInfState U) q) = 1
  rw [predCodeInfEvidence_singleton_of_satisfies pw q h]
  simp [Evidence.toStrength, Evidence.total]

theorem queryStrength_singleton_of_not_satisfies {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeInfQuery U) (h : ¬ SatisfiesInf pw q) :
    WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
        ({pw} : PredCodeInfState U) q = 0 := by
  change Evidence.toStrength (predCodeInfEvidence ({pw} : PredCodeInfState U) q) = 0
  rw [predCodeInfEvidence_singleton_of_not_satisfies pw q h]
  simp [Evidence.toStrength, Evidence.total]

theorem singleton_adequacy_strength_one {U : Type*}
    (pw : PointedPredCode U) (q : PredCodeInfQuery U) :
    SatisfiesInf pw q ↔
      WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
        ({pw} : PredCodeInfState U) q = 1 := by
  constructor
  · intro h
    exact queryStrength_singleton_of_satisfies pw q h
  · intro h
    by_cases hs : SatisfiesInf pw q
    · exact hs
    · have h0 :
          WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
              ({pw} : PredCodeInfState U) q = 0 :=
        queryStrength_singleton_of_not_satisfies pw q hs
      have h01 : (0 : ℝ≥0∞) = 1 := by
        calc
          (0 : ℝ≥0∞) =
              WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
                ({pw} : PredCodeInfState U) q := h0.symm
          _ = 1 := h
      exact False.elim (zero_ne_one h01)

def pointwiseImplies {U : Type*} (q₁ q₂ : PredCodeInfQuery U) : Prop :=
  ∀ pw : PointedPredCode U, SatisfiesInf pw q₁ → SatisfiesInf pw q₂

def singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeInfQuery U) : Prop :=
  ∀ pw : PointedPredCode U,
    WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
        ({pw} : PredCodeInfState U) q₁ ≤
      WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
        ({pw} : PredCodeInfState U) q₂

theorem pointwiseImplies_iff_singletonStrengthLE {U : Type*}
    (q₁ q₂ : PredCodeInfQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonStrengthLE q₁ q₂ := by
  constructor
  · intro himp pw
    by_cases hq₁ : SatisfiesInf pw q₁
    · have hq₂ : SatisfiesInf pw q₂ := himp pw hq₁
      rw [queryStrength_singleton_of_satisfies pw q₁ hq₁]
      rw [queryStrength_singleton_of_satisfies pw q₂ hq₂]
    · rw [queryStrength_singleton_of_not_satisfies pw q₁ hq₁]
      exact zero_le _
  · intro hle pw hq₁
    by_contra hq₂
    have hsingleton := hle pw
    have h1 :
        WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
            ({pw} : PredCodeInfState U) q₁ = 1 :=
      queryStrength_singleton_of_satisfies pw q₁ hq₁
    have h0 :
        WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U)
            ({pw} : PredCodeInfState U) q₂ = 0 :=
      queryStrength_singleton_of_not_satisfies pw q₂ hq₂
    have h10 : (1 : ℝ≥0∞) ≤ 0 := by
      have htmp := hsingleton
      rw [h1, h0] at htmp
      exact htmp
    exact not_le_of_gt (by simp : (0 : ℝ≥0∞) < 1) h10

private theorem countP_le_countP_of_imp {U : Type*}
    (W : PredCodeInfState U)
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

private theorem predCodeInfEvidence_total {U : Type*}
    (W : PredCodeInfState U) (q : PredCodeInfQuery U) :
    (predCodeInfEvidence W q).total = (W.card : ℝ≥0∞) := by
  classical
  have hcardNat :
      W.card =
        Multiset.countP (fun pw : PointedPredCode U => SatisfiesInf pw q) W +
          Multiset.countP (fun pw : PointedPredCode U => ¬ SatisfiesInf pw q) W := by
    simpa using (Multiset.card_eq_countP_add_countP
      (p := fun pw : PointedPredCode U => SatisfiesInf pw q) W)
  have hcard :
      (W.card : ℝ≥0∞) =
        (Multiset.countP (fun pw : PointedPredCode U => SatisfiesInf pw q) W : ℝ≥0∞) +
          (Multiset.countP (fun pw : PointedPredCode U => ¬ SatisfiesInf pw q) W : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  unfold predCodeInfEvidence Evidence.total
  simpa using hcard.symm

theorem queryStrength_le_of_pointwise {U : Type*}
    (W : PredCodeInfState U) (q₁ q₂ : PredCodeInfQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₂ := by
  let p₁ : PointedPredCode U → Prop := fun pw => SatisfiesInf pw q₁
  let p₂ : PointedPredCode U → Prop := fun pw => SatisfiesInf pw q₂
  letI : DecidablePred p₁ := Classical.decPred p₁
  letI : DecidablePred p₂ := Classical.decPred p₂
  have hq₁ :
      WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₁ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (predCodeInfEvidence W q₁).total = 0 then 0
      else (predCodeInfEvidence W q₁).pos / (predCodeInfEvidence W q₁).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₁ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [predCodeInfEvidence_total (W := W) (q := q₁)]
    simp [predCodeInfEvidence, p₁]
  have hq₂ :
      WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₂ =
        if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞) := by
    unfold WorldModel.queryStrength Evidence.toStrength
    change (if (predCodeInfEvidence W q₂).total = 0 then 0
      else (predCodeInfEvidence W q₂).pos / (predCodeInfEvidence W q₂).total)
        = if (W.card : ℝ≥0∞) = 0 then 0 else (Multiset.countP p₂ W : ℝ≥0∞) / (W.card : ℝ≥0∞)
    rw [predCodeInfEvidence_total (W := W) (q := q₂)]
    simp [predCodeInfEvidence, p₂]
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

/-- Infinitary conjunction elimination at the pointwise level. -/
theorem pointwise_iAnd_to_component {U : Type*}
    (F : Nat → PredCodeInfQuery U) (n : Nat) :
    pointwiseImplies (.iAnd F) (F n) := by
  intro pw h
  exact (satisfiesInf_iAnd_iff pw F).1 h n

/-- Infinitary disjunction introduction at the pointwise level. -/
theorem pointwise_component_to_iOr {U : Type*}
    (F : Nat → PredCodeInfQuery U) (n : Nat) :
    pointwiseImplies (F n) (.iOr F) := by
  intro pw h
  exact SatisfiesInf.iOr h

/-- WM inequality endpoint for countable conjunction elimination. -/
theorem queryStrength_le_iAnd_component {U : Type*}
    (W : PredCodeInfState U) (F : Nat → PredCodeInfQuery U) (n : Nat) :
    WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W (.iAnd F) ≤
      WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W (F n) :=
  queryStrength_le_of_pointwise (W := W) (q₁ := .iAnd F) (q₂ := F n)
    (pointwise_iAnd_to_component (F := F) (n := n))

/-- WM inequality endpoint for countable disjunction introduction. -/
theorem queryStrength_le_iOr_of_component {U : Type*}
    (W : PredCodeInfState U) (F : Nat → PredCodeInfQuery U) (n : Nat) :
    WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W (F n) ≤
      WorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W (.iOr F) :=
  queryStrength_le_of_pointwise (W := W) (q₁ := F n) (q₂ := .iOr F)
    (pointwise_component_to_iOr (F := F) (n := n))

end Mettapedia.Logic.PLNWorldModelPredCodeInfinitary
