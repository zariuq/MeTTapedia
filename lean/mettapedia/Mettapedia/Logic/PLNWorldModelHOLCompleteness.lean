import Mettapedia.Logic.PLNWorldModelHOL
import Mettapedia.Logic.PLNWorldModelCalculus

/-!
# HOL WM Consequence-Closure Wrappers

This module exposes implication-closure wrappers from the HOL WM instance
to `WMConsequenceRule` / `WMConsequenceRuleOn`.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLCompleteness

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelHOL
open scoped ENNReal

abbrev HOLQuery (U : Type*) := Mettapedia.Logic.PLNWorldModelHOL.HOLQuery U
abbrev PointedHOL (U : Type*) := Mettapedia.Logic.PLNWorldModelHOL.PointedHOL U
abbrev HOLState (U : Type*) := Multiset (PointedHOL U)

/-- Pointwise HOL implication between query predicates. -/
def pointwiseImplies {U : Type*} (q₁ q₂ : HOLQuery U) : Prop :=
  ∀ pw : PointedHOL U, pw.satisfies q₁ → pw.satisfies q₂

/-- Singleton-strength consequence alias for the HOL WM instance. -/
abbrev singletonStrengthLE {U : Type*} (q₁ q₂ : HOLQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelHOL.singletonStrengthLE q₁ q₂

theorem pointwiseImplies_iff_singletonStrengthLE {U : Type*}
    (q₁ q₂ : HOLQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonStrengthLE q₁ q₂ := by
  simpa [pointwiseImplies, singletonStrengthLE] using
    (Mettapedia.Logic.PLNWorldModelHOL.pointwiseImplies_iff_singletonStrengthLE
      (q₁ := q₁) (q₂ := q₂))

/-- Pointwise HOL implication lifts to a multiset WM strength inequality. -/
theorem multiset_strength_le_of_pointwise {U : Type*}
    (W : HOLState U) (q₁ q₂ : HOLQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := HOLState U) (Query := HOLQuery U) W q₁ ≤
      WorldModel.queryStrength (State := HOLState U) (Query := HOLQuery U) W q₂ := by
  exact
    Mettapedia.Logic.PLNWorldModelHOL.queryStrength_le_of_pointwise
      (W := W) (q₁ := q₁) (q₂ := q₂) himp

/-- Singleton-strength consequence lifts to multiset WM strength inequality. -/
theorem multiset_strength_le_of_singletonStrengthLE {U : Type*}
    (W : HOLState U) (q₁ q₂ : HOLQuery U)
    (hsing : singletonStrengthLE q₁ q₂) :
    WorldModel.queryStrength (State := HOLState U) (Query := HOLQuery U) W q₁ ≤
      WorldModel.queryStrength (State := HOLState U) (Query := HOLQuery U) W q₂ := by
  exact
    Mettapedia.Logic.PLNWorldModelHOL.multiset_strength_le_of_singletonStrengthLE
      (W := W) (q₁ := q₁) (q₂ := q₂) hsing

/-- Implication-closure wrapper: package pointwise HOL implication as a
global-side `WMConsequenceRule`. -/
def wmConsequenceRule_of_pointwise {U : Type*} (q₁ q₂ : HOLQuery U) :
    WMConsequenceRule (HOLState U) (HOLQuery U) where
  side := pointwiseImplies q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- Implication-closure wrapper from singleton-strength side conditions. -/
def wmConsequenceRule_of_singletonStrengthLE {U : Type*} (q₁ q₂ : HOLQuery U) :
    WMConsequenceRule (HOLState U) (HOLQuery U) where
  side := singletonStrengthLE q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact
      multiset_strength_le_of_singletonStrengthLE
        (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- State-indexed wrapper promoted from the global implication-closure rule. -/
def wmConsequenceRuleOn_of_pointwise {U : Type*} (q₁ q₂ : HOLQuery U) :
    WMConsequenceRuleOn (HOLState U) (HOLQuery U) :=
  WMConsequenceRuleOn.ofGlobal (wmConsequenceRule_of_pointwise (q₁ := q₁) (q₂ := q₂))

/-- State-indexed wrapper promoted from singleton-strength side conditions. -/
def wmConsequenceRuleOn_of_singletonStrengthLE {U : Type*} (q₁ q₂ : HOLQuery U) :
    WMConsequenceRuleOn (HOLState U) (HOLQuery U) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_singletonStrengthLE (q₁ := q₁) (q₂ := q₂))

end Mettapedia.Logic.PLNWorldModelHOLCompleteness

