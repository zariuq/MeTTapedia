import Mettapedia.Logic.PLNWorldModelFixpointClosure
import Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlap

/-!
# Policy-Aware WM Fixpoint Closure

Lift trusted-source gating and provenance-overlap fallback revision into the
generic WM fixpoint operator layer.

This module keeps the closure engine generic while adding a concrete policy
state adapter for weighted/source-aware Kripke WM states:

- policy state = `trustedGate trusted (fallbackRevision W₁ W₂)`,
- policy closure = least fixpoint closure on that adapted state,
- policy iteration = `immediateIter` on that adapted state.
-/

namespace Mettapedia.Logic.PLNWorldModelFixpointPolicy

open LO
open LO.Modal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open Mettapedia.Logic.PLNWorldModelKripkeWeighted
open Mettapedia.Logic.PLNWorldModelKripkeWeightedOverlap
open Mettapedia.Logic.EvidenceClass
open scoped ENNReal

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelKripkeWeighted.ModalQuery
abbrev WeightedState := Mettapedia.Logic.PLNWorldModelKripkeWeighted.WeightedState
abbrev PolicyRuleSet := RuleSet WeightedState ModalQuery

/-- Policy-adapted state:
first apply overlap-aware fallback revision, then trusted-source gating. -/
noncomputable def policyRevisedState
    (trusted : String → Prop) [DecidablePred trusted]
    (W₁ W₂ : WeightedState) : WeightedState :=
  trustedGate trusted (fallbackRevision W₁ W₂)

/-- Policy-aware least closure operator. -/
noncomputable def policyLeastRuleClosure
    (R : PolicyRuleSet)
    (trusted : String → Prop) [DecidablePred trusted]
    (W₁ W₂ : WeightedState)
    (seed : Set ModalQuery) : Set ModalQuery :=
  leastRuleClosure (State := WeightedState) (Query := ModalQuery)
    R (policyRevisedState trusted W₁ W₂) seed

/-- Policy-aware iterative closure dynamics. -/
noncomputable def policyImmediateIter
    (R : PolicyRuleSet)
    (trusted : String → Prop) [DecidablePred trusted]
    (W₁ W₂ : WeightedState)
    (seed : Set ModalQuery) : ℕ → Set ModalQuery :=
  immediateIter (State := WeightedState) (Query := ModalQuery)
    R (policyRevisedState trusted W₁ W₂) seed

theorem policyImmediateIter_subset_policyLeastRuleClosure
    (R : PolicyRuleSet)
    (trusted : String → Prop) [DecidablePred trusted]
    (W₁ W₂ : WeightedState)
    (seed : Set ModalQuery)
    (n : ℕ) :
    policyImmediateIter R trusted W₁ W₂ seed n ⊆
      policyLeastRuleClosure R trusted W₁ W₂ seed := by
  exact
    immediateIter_subset_leastRuleClosure
      (State := WeightedState) (Query := ModalQuery)
      (R := R) (W := policyRevisedState trusted W₁ W₂) (seed := seed) n

theorem policyLeastRuleClosure_thresholdValid
    (R : PolicyRuleSet)
    (trusted : String → Prop) [DecidablePred trusted]
    (W₁ W₂ : WeightedState)
    (seed : Set ModalQuery)
    (τ : ℝ≥0∞)
    (hSeed :
      thresholdValid (State := WeightedState) (Query := ModalQuery)
        (policyRevisedState trusted W₁ W₂) τ seed) :
    thresholdValid (State := WeightedState) (Query := ModalQuery)
      (policyRevisedState trusted W₁ W₂) τ
      (policyLeastRuleClosure R trusted W₁ W₂ seed) := by
  exact
    leastRuleClosure_thresholdValid
      (State := WeightedState) (Query := ModalQuery)
      (R := R) (W := policyRevisedState trusted W₁ W₂)
      (seed := seed) (τ := τ) hSeed

/-- Trust policy admitting all sources. -/
def trustedAll : String → Prop := fun _ => True

instance : DecidablePred trustedAll := fun _ => isTrue trivial

theorem trustedGate_trustedAll_eq (W : WeightedState) :
    trustedGate trustedAll W = W := by
  simp [trustedGate, trustedAll]

theorem policyRevisedState_eq_add_of_compatible_trustedAll
    {W₁ W₂ : WeightedState}
    (hcompat : compatible W₁ W₂) :
    policyRevisedState trustedAll W₁ W₂ = W₁ + W₂ := by
  simp [policyRevisedState, trustedGate_trustedAll_eq,
    fallbackRevision_eq_add_of_compatible, hcompat]

theorem policyRevisedState_eq_left_of_not_compatible_trustedAll
    {W₁ W₂ : WeightedState}
    (hcompat : ¬ compatible W₁ W₂) :
    policyRevisedState trustedAll W₁ W₂ = W₁ := by
  simp [policyRevisedState, trustedGate_trustedAll_eq,
    fallbackRevision_eq_left_of_not_compatible, hcompat]

theorem policyLeastRuleClosure_eq_add_of_compatible_trustedAll
    (R : PolicyRuleSet) (W₁ W₂ : WeightedState) (seed : Set ModalQuery)
    (hcompat : compatible W₁ W₂) :
    policyLeastRuleClosure R trustedAll W₁ W₂ seed =
      leastRuleClosure (State := WeightedState) (Query := ModalQuery)
        R (W₁ + W₂) seed := by
  simp [policyLeastRuleClosure,
    policyRevisedState_eq_add_of_compatible_trustedAll (hcompat := hcompat)]

theorem policyLeastRuleClosure_eq_left_of_not_compatible_trustedAll
    (R : PolicyRuleSet) (W₁ W₂ : WeightedState) (seed : Set ModalQuery)
    (hcompat : ¬ compatible W₁ W₂) :
    policyLeastRuleClosure R trustedAll W₁ W₂ seed =
      leastRuleClosure (State := WeightedState) (Query := ModalQuery)
        R W₁ seed := by
  simp [policyLeastRuleClosure,
    policyRevisedState_eq_left_of_not_compatible_trustedAll (hcompat := hcompat)]

theorem policyImmediateIter_eq_add_of_compatible_trustedAll
    (R : PolicyRuleSet) (W₁ W₂ : WeightedState) (seed : Set ModalQuery)
    (hcompat : compatible W₁ W₂) :
    policyImmediateIter R trustedAll W₁ W₂ seed =
      immediateIter (State := WeightedState) (Query := ModalQuery)
        R (W₁ + W₂) seed := by
  funext n
  simp [policyImmediateIter,
    policyRevisedState_eq_add_of_compatible_trustedAll (hcompat := hcompat)]

theorem policyImmediateIter_eq_left_of_not_compatible_trustedAll
    (R : PolicyRuleSet) (W₁ W₂ : WeightedState) (seed : Set ModalQuery)
    (hcompat : ¬ compatible W₁ W₂) :
    policyImmediateIter R trustedAll W₁ W₂ seed =
      immediateIter (State := WeightedState) (Query := ModalQuery)
        R W₁ seed := by
  funext n
  simp [policyImmediateIter,
    policyRevisedState_eq_left_of_not_compatible_trustedAll (hcompat := hcompat)]

end Mettapedia.Logic.PLNWorldModelFixpointPolicy
