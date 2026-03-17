import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelFOLInfinitary

/-!
# Infinitary FOL WM Consequence-Closure Wrappers

This module exposes implication-closure wrappers from the infinitary FOL WM
instance to `WMConsequenceRule` / `WMConsequenceRuleOn`.
-/

namespace Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness

open LO
open LO.FirstOrder
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelFOLInfinitary
open scoped ENNReal

universe u

abbrev FOLInfQuery (L : Language.{u}) := Mettapedia.Logic.PLNWorldModelFOLInfinitary.FOLInfQuery L
abbrev PointedFOL (L : Language.{u}) := Mettapedia.Logic.PLNWorldModelFOLInfinitary.PointedFOL L
abbrev FOLInfState (L : Language.{u}) := Mettapedia.Logic.PLNWorldModelFOLInfinitary.FOLInfState L

abbrev pointwiseImplies {L : Language.{u}} (q₁ q₂ : FOLInfQuery L) : Prop :=
  Mettapedia.Logic.PLNWorldModelFOLInfinitary.pointwiseImplies q₁ q₂

abbrev singletonStrengthLE {L : Language.{u}} (q₁ q₂ : FOLInfQuery L) : Prop :=
  Mettapedia.Logic.PLNWorldModelFOLInfinitary.singletonStrengthLE q₁ q₂

theorem pointwiseImplies_iff_singletonStrengthLE {L : Language.{u}}
    (q₁ q₂ : FOLInfQuery L) :
    pointwiseImplies q₁ q₂ ↔ singletonStrengthLE q₁ q₂ := by
  simpa [pointwiseImplies, singletonStrengthLE] using
    (Mettapedia.Logic.PLNWorldModelFOLInfinitary.pointwiseImplies_iff_singletonStrengthLE
      (q₁ := q₁) (q₂ := q₂))

theorem multiset_strength_le_of_pointwise {L : Language.{u}}
    (W : FOLInfState L) (q₁ q₂ : FOLInfQuery L)
    (himp : pointwiseImplies q₁ q₂) :
    BinaryWorldModel.queryStrength (State := FOLInfState L) (Query := FOLInfQuery L) W q₁ ≤
      BinaryWorldModel.queryStrength (State := FOLInfState L) (Query := FOLInfQuery L) W q₂ := by
  exact
    Mettapedia.Logic.PLNWorldModelFOLInfinitary.queryStrength_le_of_pointwise
      (W := W) (q₁ := q₁) (q₂ := q₂) himp

theorem multiset_strength_le_of_singletonStrengthLE {L : Language.{u}}
    (W : FOLInfState L) (q₁ q₂ : FOLInfQuery L)
    (hsing : singletonStrengthLE q₁ q₂) :
    BinaryWorldModel.queryStrength (State := FOLInfState L) (Query := FOLInfQuery L) W q₁ ≤
      BinaryWorldModel.queryStrength (State := FOLInfState L) (Query := FOLInfQuery L) W q₂ := by
  have himp : pointwiseImplies q₁ q₂ :=
    (pointwiseImplies_iff_singletonStrengthLE (q₁ := q₁) (q₂ := q₂)).2 hsing
  exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) himp

/-- Package pointwise infinitary FOL implication as a global consequence rule. -/
def wmConsequenceRule_of_pointwise {L : Language.{u}} (q₁ q₂ : FOLInfQuery L) :
    WMConsequenceRule (FOLInfState L) (FOLInfQuery L) where
  side := pointwiseImplies q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- Package singleton-strength side conditions as a global consequence rule. -/
def wmConsequenceRule_of_singletonStrengthLE {L : Language.{u}} (q₁ q₂ : FOLInfQuery L) :
    WMConsequenceRule (FOLInfState L) (FOLInfQuery L) where
  side := singletonStrengthLE q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact
      multiset_strength_le_of_singletonStrengthLE
        (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- State-indexed wrapper promoted from global pointwise implication rule. -/
def wmConsequenceRuleOn_of_pointwise {L : Language.{u}} (q₁ q₂ : FOLInfQuery L) :
    WMConsequenceRuleOn (FOLInfState L) (FOLInfQuery L) :=
  WMConsequenceRuleOn.ofGlobal (wmConsequenceRule_of_pointwise (q₁ := q₁) (q₂ := q₂))

/-- State-indexed wrapper promoted from global singleton-strength rule. -/
def wmConsequenceRuleOn_of_singletonStrengthLE {L : Language.{u}} (q₁ q₂ : FOLInfQuery L) :
    WMConsequenceRuleOn (FOLInfState L) (FOLInfQuery L) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_singletonStrengthLE (q₁ := q₁) (q₂ := q₂))

end Mettapedia.Logic.PLNWorldModelFOLInfinitaryCompleteness

