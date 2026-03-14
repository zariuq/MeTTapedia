import Mettapedia.Logic.PLNWorldModelPredCode
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWorldModelCategoricalBridge

/-!
# Predicate-Code WM Consequence-Closure Wrappers

This module preserves the older predicate-code consequence bridge under an
explicit `PredCode` name.
-/

namespace Mettapedia.Logic.PLNWorldModelPredCodeCompleteness

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModelPredCode
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open scoped ENNReal

/-- Alias for the unified categorical endpoint surface, specialized to predicate-code WM states. -/
abbrev WMCategoricalEndpointSurface {U : Type*}
    (H : WMHyperdoctrine (PredCodeState U)) : Prop :=
  Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine.EndpointSurface (H := H)

/-- Pointwise predicate-code implication between query predicates. -/
def pointwiseImplies {U : Type*} (q₁ q₂ : PredCodeQuery U) : Prop :=
  ∀ pw : PointedPredCode U, pw.satisfies q₁ → pw.satisfies q₂

/-- Singleton-strength consequence alias for the predicate-code WM instance. -/
abbrev singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeQuery U) : Prop :=
  Mettapedia.Logic.PLNWorldModelPredCode.singletonStrengthLE q₁ q₂

/-- Naming alias: singleton consequence on predicate-code WM states. -/
abbrev singletonConsequence {U : Type*} (q₁ q₂ : PredCodeQuery U) : Prop :=
  singletonStrengthLE q₁ q₂

theorem pointwiseImplies_iff_singletonStrengthLE {U : Type*}
    (q₁ q₂ : PredCodeQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonStrengthLE q₁ q₂ := by
  simpa [pointwiseImplies, singletonStrengthLE] using
    (Mettapedia.Logic.PLNWorldModelPredCode.pointwiseImplies_iff_singletonStrengthLE
      (q₁ := q₁) (q₂ := q₂))

/-- Naming alias for the same bridge with `singletonConsequence` terminology. -/
theorem pointwiseImplies_iff_singletonConsequence {U : Type*}
    (q₁ q₂ : PredCodeQuery U) :
    pointwiseImplies q₁ q₂ ↔ singletonConsequence q₁ q₂ :=
  pointwiseImplies_iff_singletonStrengthLE (q₁ := q₁) (q₂ := q₂)

/-- Pointwise predicate-code implication lifts to a multiset WM strength inequality. -/
theorem multiset_strength_le_of_pointwise {U : Type*}
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ := by
  exact
    Mettapedia.Logic.PLNWorldModelPredCode.queryStrength_le_of_pointwise
      (W := W) (q₁ := q₁) (q₂ := q₂) himp

/-- Naming alias: transfer from pointwise implication to multiset consequence. -/
theorem multiset_consequence_of_pointwise {U : Type*}
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ :=
  multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) himp

/-- Categorical-aligned predicate-code implication closure wrapper. -/
theorem multiset_strength_le_of_pointwise_categorical {U : Type*}
    (H : WMHyperdoctrine (PredCodeState U))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (himp : pointwiseImplies q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ :=
  multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) himp

/-- Singleton-strength consequence lifts to multiset WM strength inequality. -/
theorem multiset_strength_le_of_singletonStrengthLE {U : Type*}
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (hsing : singletonStrengthLE q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ := by
  exact
    Mettapedia.Logic.PLNWorldModelPredCode.multiset_strength_le_of_singletonStrengthLE
      (W := W) (q₁ := q₁) (q₂ := q₂) hsing

/-- Naming alias: transfer from singleton consequence to multiset consequence. -/
theorem multiset_consequence_of_singletonConsequence {U : Type*}
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (hsing : singletonConsequence q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ :=
  multiset_strength_le_of_singletonStrengthLE (W := W) (q₁ := q₁) (q₂ := q₂) hsing

/-- Proof-system-agnostic bridge schema:
if an external implication relation is sound and complete for pointwise
predicate-code implication, then it is equivalent to singleton WM consequence. -/
theorem externalImplication_iff_singletonConsequence_of_sound_complete {U : Type*}
    (ProvImp : PredCodeQuery U → PredCodeQuery U → Prop)
    (hSound : ∀ {q₁ q₂}, ProvImp q₁ q₂ → pointwiseImplies q₁ q₂)
    (hComplete : ∀ {q₁ q₂}, pointwiseImplies q₁ q₂ → ProvImp q₁ q₂)
    (q₁ q₂ : PredCodeQuery U) :
    ProvImp q₁ q₂ ↔ singletonConsequence q₁ q₂ := by
  constructor
  · intro hprov
    exact (pointwiseImplies_iff_singletonConsequence (q₁ := q₁) (q₂ := q₂)).1 (hSound hprov)
  · intro hsing
    exact hComplete ((pointwiseImplies_iff_singletonConsequence (q₁ := q₁) (q₂ := q₂)).2 hsing)

/-- Proof-system-agnostic soundness transfer:
if an external implication relation is sound w.r.t. pointwise predicate-code
implication, then it yields multiset WM consequence inequalities. -/
theorem multiset_consequence_of_externalImplication_sound {U : Type*}
    (ProvImp : PredCodeQuery U → PredCodeQuery U → Prop)
    (hSound : ∀ {q₁ q₂}, ProvImp q₁ q₂ → pointwiseImplies q₁ q₂)
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (hprov : ProvImp q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ :=
  multiset_consequence_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) (hSound hprov)

/-- Categorical-aligned predicate-code singleton-strength closure wrapper. -/
theorem multiset_strength_le_of_singletonStrengthLE_categorical {U : Type*}
    (H : WMHyperdoctrine (PredCodeState U))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (W : PredCodeState U) (q₁ q₂ : PredCodeQuery U)
    (hsing : singletonStrengthLE q₁ q₂) :
    WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₁ ≤
      WorldModel.queryStrength (State := PredCodeState U) (Query := PredCodeQuery U) W q₂ :=
  multiset_strength_le_of_singletonStrengthLE (W := W) (q₁ := q₁) (q₂ := q₂) hsing

/-- Implication-closure wrapper: package pointwise predicate-code implication as a
global-side `WMConsequenceRule`. -/
def wmConsequenceRule_of_pointwise {U : Type*} (q₁ q₂ : PredCodeQuery U) :
    WMConsequenceRule (PredCodeState U) (PredCodeQuery U) where
  side := pointwiseImplies q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact multiset_strength_le_of_pointwise (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- Implication-closure wrapper from singleton-strength side conditions. -/
def wmConsequenceRule_of_singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeQuery U) :
    WMConsequenceRule (PredCodeState U) (PredCodeQuery U) where
  side := singletonStrengthLE q₁ q₂
  premise := q₁
  conclusion := q₂
  sound := by
    intro hSide W
    exact
      multiset_strength_le_of_singletonStrengthLE
        (W := W) (q₁ := q₁) (q₂ := q₂) hSide

/-- State-indexed wrapper promoted from the global implication-closure rule. -/
def wmConsequenceRuleOn_of_pointwise {U : Type*} (q₁ q₂ : PredCodeQuery U) :
    WMConsequenceRuleOn (PredCodeState U) (PredCodeQuery U) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_pointwise (q₁ := q₁) (q₂ := q₂))

/-- Categorical-aligned state-indexed wrapper from predicate-code pointwise implication. -/
def wmConsequenceRuleOn_of_pointwise_categorical {U : Type*}
    (H : WMHyperdoctrine (PredCodeState U))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (q₁ q₂ : PredCodeQuery U) :
    WMConsequenceRuleOn (PredCodeState U) (PredCodeQuery U) :=
  wmConsequenceRuleOn_of_pointwise (q₁ := q₁) (q₂ := q₂)

/-- State-indexed wrapper promoted from singleton-strength side conditions. -/
def wmConsequenceRuleOn_of_singletonStrengthLE {U : Type*} (q₁ q₂ : PredCodeQuery U) :
    WMConsequenceRuleOn (PredCodeState U) (PredCodeQuery U) :=
  WMConsequenceRuleOn.ofGlobal
    (wmConsequenceRule_of_singletonStrengthLE (q₁ := q₁) (q₂ := q₂))

/-- Categorical-aligned state-indexed wrapper from predicate-code singleton-strength side
conditions. -/
def wmConsequenceRuleOn_of_singletonStrengthLE_categorical {U : Type*}
    (H : WMHyperdoctrine (PredCodeState U))
    (_hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (_φc : H.query X)
    (q₁ q₂ : PredCodeQuery U) :
    WMConsequenceRuleOn (PredCodeState U) (PredCodeQuery U) :=
  wmConsequenceRuleOn_of_singletonStrengthLE (q₁ := q₁) (q₂ := q₂)

end Mettapedia.Logic.PLNWorldModelPredCodeCompleteness
