import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelHOLInfinitary

/-!
# Infinitary HOL WM Consequence-Closure Wrappers

This module exposes implication-closure wrappers from the infinitary HOL WM
instance to `WMConsequenceRule` / `WMConsequenceRuleOn`.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelHOLInfinitary
open scoped ENNReal

abbrev HOLInfQuery (U : Type*) := Mettapedia.Logic.PLNWorldModelHOLInfinitary.HOLInfQuery U
abbrev PointedHOL (U : Type*) := Mettapedia.Logic.PLNWorldModelHOLInfinitary.PointedHOL U
abbrev HOLInfState (U : Type*) := Mettapedia.Logic.PLNWorldModelHOLInfinitary.HOLInfState U

abbrev pointwiseImplies {U : Type*} (q₁ q₂ : HOLInfQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelHOLInfinitary.pointwiseImplies q₁ q₂

abbrev singletonStrengthLE {U : Type*} (q₁ q₂ : HOLInfQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelHOLInfinitary.singletonStrengthLE q₁ q₂

theorem pointwiseImplies_iff_singletonStrengthLE {U : Type*}
    (q₁ q₂ : HOLInfQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonStrengthLE q₁ q₂ := by
  simpa [pointwiseImplies, singletonStrengthLE] using
    (Mettapedia.Logic.PLNWorldModelHOLInfinitary.pointwiseImplies_iff_singletonStrengthLE
      (q₁ := q₁) (q₂ := q₂))

theorem multiset_strength_le_of_pointwise {U : Type*}
    (W : HOLInfState U) (q₁ q₂ : HOLInfQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := HOLInfState U) (Query := HOLInfQuery U) W q₁ ≤
      WorldModel.queryStrength (State := HOLInfState U) (Query := HOLInfQuery U) W q₂ := by
  exact
    Mettapedia.Logic.PLNWorldModelHOLInfinitary.queryStrength_le_of_pointwise
      (W := W) (q₁ := q₁) (q₂ := q₂) himp

theorem multiset_strength_le_of_singletonStrengthLE {U : Type*}
    (W : HOLInfState U) (q₁ q₂ : HOLInfQuery U)
    (hsing : singletonStrengthLE q₁ q₂) :
    WorldModel.queryStrength (State := HOLInfState U) (Query := HOLInfQuery U) W q₁ ≤
      WorldModel.queryStrength (State := HOLInfState U) (Query := HOLInfQuery U) W q₂ := by
  have himp : pointwiseImplies q₁ q₂ :=
    (pointwiseImplies_iff_singletonStrengthLE (q₁ := q₁) (q₂ := q₂)).2 hsing
  exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) himp

/-- Package pointwise infinitary HOL implication as a global consequence rule. -/
def wmConsequenceRule_of_pointwise {U : Type*} (q₁ q₂ : HOLInfQuery U) :
    WMConsequenceRule (HOLInfState U) (HOLInfQuery U) where
  side := pointwiseImplies q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- Package singleton-strength side conditions as a global consequence rule. -/
def wmConsequenceRule_of_singletonStrengthLE {U : Type*} (q₁ q₂ : HOLInfQuery U) :
    WMConsequenceRule (HOLInfState U) (HOLInfQuery U) where
  side := singletonStrengthLE q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact
      multiset_strength_le_of_singletonStrengthLE
        (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- State-indexed wrapper promoted from global pointwise implication rule. -/
def wmConsequenceRuleOn_of_pointwise {U : Type*} (q₁ q₂ : HOLInfQuery U) :
    WMConsequenceRuleOn (HOLInfState U) (HOLInfQuery U) :=
  WMConsequenceRuleOn.ofGlobal (wmConsequenceRule_of_pointwise (q₁ := q₁) (q₂ := q₂))

/-- State-indexed wrapper promoted from global singleton-strength rule. -/
def wmConsequenceRuleOn_of_singletonStrengthLE {U : Type*} (q₁ q₂ : HOLInfQuery U) :
    WMConsequenceRuleOn (HOLInfState U) (HOLInfQuery U) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_singletonStrengthLE (q₁ := q₁) (q₂ := q₂))

end Mettapedia.Logic.PLNWorldModelHOLInfinitaryCompleteness

