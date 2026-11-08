import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalCheckingTower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingBoundary

/-!
# Normalization enters the checking fragment without claiming subject expansion

A well-typed raw checker counterexample is outside the bidirectional
fragment. Its independently typed reduct is inside. Conversely a stuck
normal application of a pair has no type: normality alone is insufficient.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalChecking.Controls

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

abbrev setting := ConversionControls.setting

theorem lambda_not_in_synthesis {n : Nat} (body : Tower.Tm (n + 1)) :
    ¬ Bidirectional .synth (.lam body) := by intro impossible; cases impossible

theorem typed_raw_counterexample_outside_fragment :
    Typed Tower.rules .nil ContextualDependentCheckingBoundary.redex
      ContextualDependentCheckingBoundary.functionCode ∧
    ¬ Bidirectional .check ContextualDependentCheckingBoundary.redex := by
  refine ⟨ContextualDependentCheckingBoundary.redex_typed, ?_⟩
  intro checkable
  cases checkable with
  | synthesized synthesis =>
      cases synthesis with
      | app function _ => exact lambda_not_in_synthesis _ function
      | redex _ argument => exact lambda_not_in_synthesis _ argument

def normalizedInput : TotalTerm (empty Tower.rules) :=
  ContextualDependentNormalization.termAt (S := setting) (fun _ => none)
    TowerModel.facts TowerModel.roots TowerModel.heads 2
    ⟨ContextualDependentCheckingBoundary.functionType, ContextualDependentCheckingBoundary.typedRedex⟩

theorem real_reduction_enters_fragment :
    normalizedInput.2.code = ContextualDependentCheckingBoundary.identity.code ∧
    ContextualDependentNormalCheckingTower.Ready (fun _ => (0 : Nat)) normalizedInput := by
  refine ⟨by rfl', ContextualDependentNormalCheckingTower.ready_of_normal _ _ ?_⟩
  constructor
  · exact ContextualDependentReductionBudget.normal_of_stopped Tower.rules (fun _ => none)
      (fun _ _ _ impossible => impossible.elim) _ (by rfl')
  · exact ContextualDependentReductionBudget.normal_of_stopped Tower.rules (fun _ => none)
      (fun _ _ _ impossible => impossible.elim) _ (by rfl')

theorem normalized_value_is_executably_checked :
    (ExecutableChecking.check Tower.rules ExecutableTowerChoices.choices ConversionControls.reducer 16
      .nil normalizedInput.2.code normalizedInput.1.code).isSome = true := by rfl'

def stuck : Tower.Tm 0 :=
  .app (.pair (.head .legacyGround) (.head .legacyGround)) (.head .legacyGround)

theorem stuck_is_normal : Normal (S := setting) stuck :=
  ContextualDependentReductionBudget.normal_of_stopped Tower.rules (fun _ => none)
    (fun _ _ _ impossible => impossible.elim) _ (by rfl')

theorem stuck_has_no_type (type : Tower.Tm 0) : ¬ Typed Tower.rules .nil stuck type := by
  intro typed
  obtain ⟨domain, codomain, functionTyped, _, _⟩ := typed.generation
  obtain ⟨domain', codomain', same⟩ := pair_type (S := setting) TowerModel.facts .nil functionTyped
  exact TypeEq.pi_ne_sigma TowerModel.facts .nil same

theorem untyped_normal_form_outside_fragment : ¬ Bidirectional .check stuck := by
  intro checkable
  cases checkable with
  | synthesized synthesis =>
      cases synthesis with
      | app function _ => cases function

end ContextualDependentNormalChecking.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
