import Mettapedia.Logic.PLNWorldModelFOLCompleteness
import Foundation.FirstOrder.SetTheory.Universe
import Mettapedia.Logic.PLNWorldModelCategoricalBridge

/-!
# Set-Theory ↔ WM Consequence Bridge

This module specializes the generic FOL↔WM bridge to Foundation's set-theory
language `ℒₛₑₜ` and standard theories (`𝗭`, `𝗭𝗙`, `𝗭𝗖`, `𝗭𝗙𝗖`).

Interpretation:

- Set-theoretic semantic consequence/provability lives in Foundation FOL.
- WM consequence inequalities are derived as a sound target semantics.
- For implication queries, singleton WM consequence on `T`-models is equivalent
  to Foundation provability.

This gives a precise "WM as semantic lens on set-theoretic semantics" statement
for the implication fragment.
-/

namespace Mettapedia.Logic.PLNWorldModelSetTheoryBridge

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelFOLCompleteness
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine

abbrev SetLang := ℒₛₑₜ
abbrev SetTheory := Theory SetLang
abbrev SetQuery := FOLQuery SetLang
abbrev SetPointed := PointedFOL SetLang
abbrev SetState := FOLState SetLang

abbrev WMCategoricalEndpointSurface
    (H : WMHyperdoctrine SetState) : Prop :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.WMCategoricalEndpointSurface (H := H)

/-- Set-theory model-side condition for WM states. -/
abbrev stateModelsTheory (T : SetTheory) (W : SetState) : Prop :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.stateModelsTheory T W

/-- Set-theory singleton-strength consequence schema. -/
abbrev singletonStrengthLEOnTheory (T : SetTheory) (φ ψ : SetQuery) : Prop :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.singletonStrengthLEOnTheory T φ ψ

/-- Set-theory pointwise implication on `T`-models. -/
abbrev pointwiseImpliesOnTheory (T : SetTheory) (φ ψ : SetQuery) : Prop :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.pointwiseImpliesOnTheory T φ ψ

/-- Set-theoretic semantic consequence iff singleton WM consequence (implication
fragment). -/
theorem consequence_iff_singletonStrengthLEOnTheory
    (T : SetTheory) (φ ψ : SetQuery) :
    T ⊨[SmallStruc SetLang] (φ ➝ ψ) ↔ singletonStrengthLEOnTheory T φ ψ := by
  simpa [SetLang, SetQuery, SetTheory] using
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.consequence_iff_singletonStrengthLEOnTheory
      (L := SetLang) (T := T) (φ := φ) (ψ := ψ))

/-- Set-theoretic provability iff singleton WM consequence (implication
fragment). -/
theorem provable_imp_iff_singletonStrengthLEOnTheory
    (T : SetTheory) (φ ψ : SetQuery) :
    (T ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOnTheory T φ ψ := by
  simpa [SetLang, SetQuery, SetTheory] using
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.provable_imp_iff_singletonStrengthLEOnTheory
      (L := SetLang) (T := T) (φ := φ) (ψ := ψ))

/-- Steelman singleton-explicit form:
set-theoretic semantic consequence is equivalent to universal singleton WM
strength inequality over all pointed models of `T`. -/
theorem consequence_iff_all_model_singleton_strength
    (T : SetTheory) (φ ψ : SetQuery) :
    T ⊨[SmallStruc SetLang] (φ ➝ ψ) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ := by
  simpa [singletonStrengthLEOnTheory] using
    (consequence_iff_singletonStrengthLEOnTheory (T := T) (φ := φ) (ψ := ψ))

/-- Steelman singleton-explicit form:
set-theoretic provability is equivalent to universal singleton WM
strength inequality over all pointed models of `T`. -/
theorem provable_imp_iff_all_model_singleton_strength
    (T : SetTheory) (φ ψ : SetQuery) :
    (T ⊢ (φ ➝ ψ)) ↔
      ∀ S : SetPointed, S ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ := by
  simpa [singletonStrengthLEOnTheory] using
    (provable_imp_iff_singletonStrengthLEOnTheory (T := T) (φ := φ) (ψ := ψ))

/-- Set-theoretic semantic implication consequence gives multiset WM strength
inequality on `T`-states. -/
theorem multiset_strength_le_of_consequence
    (T : SetTheory) (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsTheory T W)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ := by
  simpa [SetLang, SetState, SetQuery, SetTheory] using
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.multiset_strength_le_of_consequence
      (L := SetLang) (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons)

/-- Set-theoretic provability transport to multiset WM consequence. -/
theorem multiset_strength_le_of_provable_imp
    (T : SetTheory) (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ := by
  simpa [SetLang, SetState, SetQuery, SetTheory] using
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.multiset_strength_le_of_provable_imp
      (L := SetLang) (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov)

/-- Singleton negative criterion:
if a pointed structure satisfies `φ` but not `ψ`, singleton WM strength inequality
fails on that structure. -/
theorem singleton_strength_not_of_satisfies_and_not_satisfies
    (S : SetPointed) (φ ψ : SetQuery)
    (hφ : Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S φ)
    (hnotψ : ¬ Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S ψ) :
    ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
          ({S} : SetState) φ ≤
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
          ({S} : SetState) ψ) := by
  intro hle
  have himp :=
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.singletonStrengthLE_singleton_iff_imp
      (S := S) (φ := φ) (ψ := ψ)).1 hle
  exact hnotψ (himp hφ)

/-- Outside-theory-scope counterexample family:
for a pointed structure not modeling `T`, singleton WM inequalities may fail even
when we only care about `T`-models in the bridge. -/
theorem singleton_outside_theory_scope_counterexample
    (T : SetTheory) (S : SetPointed) (φ ψ : SetQuery)
    (hNotModel : ¬ S ⊧* T)
    (hφ : Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S φ)
    (hnotψ : ¬ Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S ψ) :
    ¬ stateModelsTheory T ({S} : SetState) ∧
      ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ) := by
  constructor
  · intro hstate
    exact hNotModel (hstate S (by simp))
  · exact singleton_strength_not_of_satisfies_and_not_satisfies
      (S := S) (φ := φ) (ψ := ψ) hφ hnotψ

/-- Full steelman split for Set↔WM implication transport:
positive exactness on theory models plus explicit outside-theory failure family. -/
theorem set_to_wm_expressivity_split
    (T : SetTheory) (φ ψ : SetQuery) (S : SetPointed)
    (hNotModel : ¬ S ⊧* T)
    (hφ : Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S φ)
    (hnotψ : ¬ Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S ψ) :
    ((T ⊢ (φ ➝ ψ)) ↔
      ∀ S' : SetPointed, S' ⊧* T →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S'} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S'} : SetState) ψ)
    ∧
    (¬ stateModelsTheory T ({S} : SetState) ∧
      ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ)) := by
  constructor
  · exact provable_imp_iff_all_model_singleton_strength (T := T) (φ := φ) (ψ := ψ)
  · exact singleton_outside_theory_scope_counterexample
      (T := T) (S := S) (φ := φ) (ψ := ψ) hNotModel hφ hnotψ

/-- Unified endpoint pack:
from set-theoretic provability, we get WM multiset consequence transfer and the
categorical endpoint surface in one theorem. -/
theorem provable_imp_to_multiset_and_endpoint_surface
    (H : WMHyperdoctrine SetState)
    (T : SetTheory) (φ ψ : SetQuery)
    (hprov : T ⊢ (φ ➝ ψ)) :
    (∀ W : SetState, stateModelsTheory T W →
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ)
    ∧
    EndpointSurface (H := H) := by
  constructor
  · intro W hW
    exact multiset_strength_le_of_provable_imp
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov
  · exact endpointSurface_of_hyperdoctrine (H := H)

/-- Set-theory consequence packaged as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_consequence
    (T : SetTheory) (φ ψ : SetQuery)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.wmConsequenceRuleOn_of_consequence
    (L := SetLang) (T := T) (φ := φ) (ψ := ψ) hcons

/-- Set-theory provability packaged as a state-indexed WM consequence rule. -/
def wmConsequenceRuleOn_of_provable_imp
    (T : SetTheory) (φ ψ : SetQuery)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.wmConsequenceRuleOn_of_provable_imp
    (L := SetLang) (T := T) (φ := φ) (ψ := ψ) hprov

/-- Categorical-aligned set-theory consequence wrapper. -/
theorem multiset_strength_le_of_consequence_categorical
    (H : WMHyperdoctrine SetState)
    (hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (φc : H.query X)
    (T : SetTheory) (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsTheory T W)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ := by
  simpa [SetLang, SetState, SetQuery, SetTheory] using
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.multiset_strength_le_of_consequence_categorical
      (L := SetLang) (H := H) (_hcat := hcat) (X := X) (_φc := φc)
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hcons)

/-- Categorical-aligned set-theory provability wrapper. -/
theorem multiset_strength_le_of_provable_imp_categorical
    (H : WMHyperdoctrine SetState)
    (hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (φc : H.query X)
    (T : SetTheory) (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsTheory T W)
    (hprov : T ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ := by
  simpa [SetLang, SetState, SetQuery, SetTheory] using
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.multiset_strength_le_of_provable_imp_categorical
      (L := SetLang) (H := H) (_hcat := hcat) (X := X) (_φc := φc)
      (T := T) (W := W) (φ := φ) (ψ := ψ) hW hprov)

/-- Categorical-aligned packaging from semantic consequence. -/
def wmConsequenceRuleOn_of_consequence_categorical
    (H : WMHyperdoctrine SetState)
    (hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (φc : H.query X)
    (T : SetTheory) (φ ψ : SetQuery)
    (hcons : T ⊨[SmallStruc SetLang] (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.wmConsequenceRuleOn_of_consequence_categorical
    (L := SetLang) (H := H) (_hcat := hcat) (X := X) (_φc := φc)
    (T := T) (φ := φ) (ψ := ψ) hcons

/-- Categorical-aligned packaging from provable implication. -/
def wmConsequenceRuleOn_of_provable_imp_categorical
    (H : WMHyperdoctrine SetState)
    (hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (φc : H.query X)
    (T : SetTheory) (φ ψ : SetQuery)
    (hprov : T ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  Mettapedia.Logic.PLNWorldModelFOLCompleteness.wmConsequenceRuleOn_of_provable_imp_categorical
    (L := SetLang) (H := H) (_hcat := hcat) (X := X) (_φc := φc)
    (T := T) (φ := φ) (ψ := ψ) hprov

/-! ## Concrete theory wrappers (Z, ZF, ZC, ZFC) -/

abbrev stateModelsZ : SetState → Prop := stateModelsTheory 𝗭
abbrev stateModelsZF : SetState → Prop := stateModelsTheory 𝗭𝗙
abbrev stateModelsZC : SetState → Prop := stateModelsTheory 𝗭𝗖
abbrev stateModelsZFC : SetState → Prop := stateModelsTheory 𝗭𝗙𝗖

theorem provable_imp_iff_singletonStrengthLEOnZ
    (φ ψ : SetQuery) :
    (𝗭 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOnTheory 𝗭 φ ψ :=
  provable_imp_iff_singletonStrengthLEOnTheory (T := 𝗭) (φ := φ) (ψ := ψ)

theorem provable_imp_iff_singletonStrengthLEOnZF
    (φ ψ : SetQuery) :
    (𝗭𝗙 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOnTheory 𝗭𝗙 φ ψ :=
  provable_imp_iff_singletonStrengthLEOnTheory (T := 𝗭𝗙) (φ := φ) (ψ := ψ)

theorem provable_imp_iff_singletonStrengthLEOnZC
    (φ ψ : SetQuery) :
    (𝗭𝗖 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOnTheory 𝗭𝗖 φ ψ :=
  provable_imp_iff_singletonStrengthLEOnTheory (T := 𝗭𝗖) (φ := φ) (ψ := ψ)

theorem provable_imp_iff_singletonStrengthLEOnZFC
    (φ ψ : SetQuery) :
    (𝗭𝗙𝗖 ⊢ (φ ➝ ψ)) ↔ singletonStrengthLEOnTheory 𝗭𝗙𝗖 φ ψ :=
  provable_imp_iff_singletonStrengthLEOnTheory (T := 𝗭𝗙𝗖) (φ := φ) (ψ := ψ)

theorem multiset_strength_le_of_provable_imp_ZF
    (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsZF W)
    (hprov : 𝗭𝗙 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ :=
  multiset_strength_le_of_provable_imp (T := 𝗭𝗙) (W := W) (φ := φ) (ψ := ψ) hW hprov

theorem multiset_strength_le_of_provable_imp_ZFC
    (W : SetState) (φ ψ : SetQuery)
    (hW : stateModelsZFC W)
    (hprov : 𝗭𝗙𝗖 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ :=
  multiset_strength_le_of_provable_imp (T := 𝗭𝗙𝗖) (W := W) (φ := φ) (ψ := ψ) hW hprov

def wmConsequenceRuleOn_of_provable_imp_ZF
    (φ ψ : SetQuery) (hprov : 𝗭𝗙 ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  wmConsequenceRuleOn_of_provable_imp (T := 𝗭𝗙) (φ := φ) (ψ := ψ) hprov

def wmConsequenceRuleOn_of_provable_imp_ZFC
    (φ ψ : SetQuery) (hprov : 𝗭𝗙𝗖 ⊢ (φ ➝ ψ)) :
    WMConsequenceRuleOn SetState SetQuery :=
  wmConsequenceRuleOn_of_provable_imp (T := 𝗭𝗙𝗖) (φ := φ) (ψ := ψ) hprov

/-- Category-facing endpoint: set-theory WM hyperdoctrines satisfy the unified
institution/Beck-Chevalley endpoint surface. -/
theorem categorical_endpoint_surface
    (H : WMHyperdoctrine SetState) :
    EndpointSurface (H := H) :=
  endpointSurface_of_hyperdoctrine (H := H)

end Mettapedia.Logic.PLNWorldModelSetTheoryBridge
