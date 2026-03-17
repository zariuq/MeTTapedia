import Mettapedia.Logic.PLNWorldModelSetTheoryBridge

/-!
# Set-Theory ↔ WM Bridge Regression Fixtures

Concrete theorem fixtures consuming the set-theory bridge endpoints.
-/

namespace Mettapedia.Logic.PLNWorldModelSetTheoryBridgeRegression

open LO
open LO.FirstOrder
open LO.FirstOrder.SetTheory
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelSetTheoryBridge
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open Mettapedia.Logic.PLNWorldModelCategoricalBridge.WMHyperdoctrine

/-- Positive fixture:
derive `𝗭𝗙 ⊢ (⊥ ➝ ⊤)` via singleton-strength bridge, package it as a WM rule,
and execute it on a singleton set-theory WM state. -/
theorem zf_bottom_to_top_rule_singleton_fixture
    (S : SetPointed)
    (hS : S ⊧* 𝗭𝗙) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) ({S} : SetState) (⊥ : SetQuery) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) ({S} : SetState) (⊤ : SetQuery) := by
  let φ : SetQuery := (⊥ : SetQuery)
  let ψ : SetQuery := (⊤ : SetQuery)
  have hpoint : pointwiseImpliesOnTheory 𝗭𝗙 φ ψ := by
    intro S' _hT hφ
    exact False.elim (by simpa [φ] using hφ)
  have hsing : singletonStrengthLEOnTheory 𝗭𝗙 φ ψ :=
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
      (T := 𝗭𝗙) (φ := φ) (ψ := ψ)).1 hpoint
  have hprov : 𝗭𝗙 ⊢ (φ ➝ ψ) :=
    (provable_imp_iff_singletonStrengthLEOnZF (φ := φ) (ψ := ψ)).2 hsing
  let rule := wmConsequenceRuleOn_of_provable_imp_ZF (φ := φ) (ψ := ψ) hprov
  have hside : rule.side ({S} : SetState) := by
    intro S' hmem
    have hEq : S' = S := by
      simpa using (List.mem_singleton.mp hmem)
    cases hEq
    simpa using hS
  simpa [rule, φ, ψ] using (rule.sound hside)

/-- Categorical fixture:
consume the categorical set-theory provability wrapper endpoint. -/
theorem zf_bottom_to_top_categorical_singleton_fixture
    (H : WMHyperdoctrine SetState)
    (hcat : WMCategoricalEndpointSurface (H := H))
    {X : H.Obj} (φc : H.query X)
    (S : SetPointed)
    (hS : S ⊧* 𝗭𝗙) :
    BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) ({S} : SetState) (⊥ : SetQuery) ≤
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) ({S} : SetState) (⊤ : SetQuery) := by
  let φ : SetQuery := (⊥ : SetQuery)
  let ψ : SetQuery := (⊤ : SetQuery)
  have hpoint : pointwiseImpliesOnTheory 𝗭𝗙 φ ψ := by
    intro S' _hT hφ
    exact False.elim (by simpa [φ] using hφ)
  have hsing : singletonStrengthLEOnTheory 𝗭𝗙 φ ψ :=
    (Mettapedia.Logic.PLNWorldModelFOLCompleteness.pointwiseImpliesOnTheory_iff_singletonStrengthLEOnTheory
      (T := 𝗭𝗙) (φ := φ) (ψ := ψ)).1 hpoint
  have hprov : 𝗭𝗙 ⊢ (φ ➝ ψ) :=
    (provable_imp_iff_singletonStrengthLEOnZF (φ := φ) (ψ := ψ)).2 hsing
  have hW : stateModelsZF ({S} : SetState) := by
    intro S' hmem
    have hEq : S' = S := by
      simpa using (List.mem_singleton.mp hmem)
    cases hEq
    simpa using hS
  exact
    multiset_strength_le_of_provable_imp_categorical
      (H := H) (hcat := hcat) (X := X) (φc := φc)
      (T := 𝗭𝗙) (W := ({S} : SetState)) (φ := φ) (ψ := ψ) hW hprov

/-- Steelman positive fixture:
explicit singleton-universal characterization for ZF in the implication fragment. -/
theorem zf_provable_iff_all_model_singleton_strength_fixture
    (φ ψ : SetQuery) :
    (𝗭𝗙 ⊢ (φ ➝ ψ)) ↔
      ∀ S : SetPointed, S ⊧* 𝗭𝗙 →
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) φ ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) ψ := by
  simpa using
    (provable_imp_iff_all_model_singleton_strength (T := 𝗭𝗙) (φ := φ) (ψ := ψ))

/-- Steelman negative fixture:
outside ZF-model side conditions, singleton WM inequalities can fail. -/
theorem zf_outside_scope_top_bottom_counterexample_fixture
    (S : SetPointed)
    (hNotModel : ¬ S ⊧* 𝗭𝗙) :
    ¬ stateModelsZF ({S} : SetState) ∧
      ¬ (BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) (⊤ : SetQuery) ≤
          BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery)
            ({S} : SetState) (⊥ : SetQuery)) := by
  have hTop : Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S (⊤ : SetQuery) := by
    simp [Mettapedia.Logic.PLNWorldModelFOL.folSatisfies]
  have hBot : ¬ Mettapedia.Logic.PLNWorldModelFOL.folSatisfies S (⊥ : SetQuery) := by
    simp [Mettapedia.Logic.PLNWorldModelFOL.folSatisfies]
  simpa [stateModelsZF] using
    (singleton_outside_theory_scope_counterexample
      (T := 𝗭𝗙) (S := S) (φ := (⊤ : SetQuery)) (ψ := (⊥ : SetQuery))
      hNotModel hTop hBot)

/-- Unified endpoint fixture:
provability transport plus categorical endpoint surface in one theorem call. -/
theorem zf_provable_to_multiset_and_endpoint_surface_fixture
    (H : WMHyperdoctrine SetState)
    (φ ψ : SetQuery)
    (hprov : 𝗭𝗙 ⊢ (φ ➝ ψ)) :
    (∀ W : SetState, stateModelsZF W →
      BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W φ ≤
        BinaryWorldModel.queryStrength (State := SetState) (Query := SetQuery) W ψ)
    ∧
    EndpointSurface (H := H) := by
  simpa [stateModelsZF] using
    (provable_imp_to_multiset_and_endpoint_surface
      (H := H) (T := 𝗭𝗙) (φ := φ) (ψ := ψ) hprov)

end Mettapedia.Logic.PLNWorldModelSetTheoryBridgeRegression
