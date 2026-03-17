import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelPredCodeInfinitary

/-!
# Infinitary Predicate-Code WM Consequence-Closure Wrappers
-/

namespace Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelPredCodeInfinitary
open scoped ENNReal

abbrev PredCodeInfQuery (U : Type*) :=
  Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.PredCodeInfQuery U
abbrev PointedPredCode (U : Type*) :=
  Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.PointedPredCode U
abbrev PredCodeInfState (U : Type*) :=
  Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.PredCodeInfState U

abbrev pointwiseImplies {U : Type*} (q₁ q₂ : PredCodeInfQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.pointwiseImplies q₁ q₂

abbrev singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeInfQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.singletonStrengthLE q₁ q₂

theorem pointwiseImplies_iff_singletonStrengthLE {U : Type*}
    (q₁ q₂ : PredCodeInfQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonStrengthLE q₁ q₂ := by
  simpa [pointwiseImplies, singletonStrengthLE] using
    (Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.pointwiseImplies_iff_singletonStrengthLE
      (q₁ := q₁) (q₂ := q₂))

theorem multiset_strength_le_of_pointwise {U : Type*}
    (W : PredCodeInfState U) (q₁ q₂ : PredCodeInfQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    BinaryWorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₁ ≤
      BinaryWorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₂ := by
  exact
    Mettapedia.Logic.PLNWorldModelPredCodeInfinitary.queryStrength_le_of_pointwise
      (W := W) (q₁ := q₁) (q₂ := q₂) himp

theorem multiset_strength_le_of_singletonStrengthLE {U : Type*}
    (W : PredCodeInfState U) (q₁ q₂ : PredCodeInfQuery U)
    (hsing : singletonStrengthLE q₁ q₂) :
    BinaryWorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₁ ≤
      BinaryWorldModel.queryStrength (State := PredCodeInfState U) (Query := PredCodeInfQuery U) W q₂ := by
  have himp : pointwiseImplies q₁ q₂ :=
    (pointwiseImplies_iff_singletonStrengthLE (q₁ := q₁) (q₂ := q₂)).2 hsing
  exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) himp

/-- Package pointwise infinitary predicate-code implication as a global consequence rule. -/
def wmConsequenceRule_of_pointwise {U : Type*} (q₁ q₂ : PredCodeInfQuery U) :
    WMConsequenceRule (PredCodeInfState U) (PredCodeInfQuery U) where
  side := pointwiseImplies q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- Package singleton-strength side conditions as a global consequence rule. -/
def wmConsequenceRule_of_singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeInfQuery U) :
    WMConsequenceRule (PredCodeInfState U) (PredCodeInfQuery U) where
  side := singletonStrengthLE q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact
      multiset_strength_le_of_singletonStrengthLE
        (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- State-indexed wrapper promoted from global pointwise implication rule. -/
def wmConsequenceRuleOn_of_pointwise {U : Type*} (q₁ q₂ : PredCodeInfQuery U) :
    WMConsequenceRuleOn (PredCodeInfState U) (PredCodeInfQuery U) :=
  WMConsequenceRuleOn.ofGlobal (wmConsequenceRule_of_pointwise (q₁ := q₁) (q₂ := q₂))

/-- State-indexed wrapper promoted from global singleton-strength rule. -/
def wmConsequenceRuleOn_of_singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeInfQuery U) :
    WMConsequenceRuleOn (PredCodeInfState U) (PredCodeInfQuery U) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_singletonStrengthLE (q₁ := q₁) (q₂ := q₂))

end Mettapedia.Logic.PLNWorldModelPredCodeInfinitaryCompleteness
