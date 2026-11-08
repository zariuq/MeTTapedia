import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingBoundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexControls

/-!
# The flexible-variable solver handles the raw-checker counterexample

The right endpoint carries an independent typing derivation. The former
raw-recovery path fails at every budget, while normalized recovery computes
the identity function and earns a principal answer for the original redex
equation. No unchecked source is assigned a type by normalization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFlex.NormalizedControls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ConversionControls.setting
abbrev type := ContextualDependentCheckingBoundary.functionType
abbrev frame := extend (empty Tower.rules) type
def viewedType : TypeOver frame := type.reindex (projectionHom _ type)
def left : Term frame viewedType := newest _ type
def right : Term frame viewedType := ContextualDependentCheckingBoundary.typedRedex.reindex (projectionHom _ type)

instance : DecidableRel setting.R.headEq := fun left right => LevelTower.instDecidableHeadEq left right
instance : DecidableRel setting.R.cumulative := fun left right => LevelTower.instDecidableCumulative left right
instance (head : Tower.Head) : Decidable (setting.R.isUniverse head) :=
  inferInstanceAs (Decidable (Tower.IsUniverse head))

theorem raw_inverse_finds_the_redex :
    ContextualDependentInversion.invert
      (ContextualDependentInversion.lookup (withoutNewest (empty Tower.rules) type).forward) right.code =
        some ContextualDependentCheckingBoundary.redex := by rfl'

set_option backward.isDefEq.respectTransparency false in
theorem raw_recovery_fails_at_every_budget (fuel : Nat) :
    ContextualDependentTypedInversion.recover (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra Controls.declarations_formed ExecutableTowerChoices.choices ConversionControls.reducer
      fuel (withoutNewest (empty Tower.rules) type) type right.code = none := by
  unfold ContextualDependentTypedInversion.recover
  split
  · rfl
  · rename_i body found
    have same := Option.some.inj (found.symm.trans raw_inverse_finds_the_redex)
    subst body
    have finish {α β : Type} {action : Option α} (stopped : action = none) (next : α → Option β) :
        action.bind next = none := by rw [stopped]; rfl
    exact finish (ContextualDependentCheckingBoundary.redex_never_checks fuel) _

def run (fuel : Nat) := stepNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra Controls.declarations_formed ExecutableTowerChoices.choices ConversionControls.reducer
  fuel left right []

theorem normalized_rule_finishes : (run 24).remaining = [] := by decide +kernel

theorem normalized_rule_has_empty_target : (run 24).target = empty Tower.rules := by rfl'

theorem normalized_rule_returns_identity : (run 24).answer.substitution 0 = .lam (.var 0) := by rfl'

theorem original_redex_equation_has_principal_answer :
    (frames setting.levels).Principal [equation left right] (run 24).answer :=
  (run 24).completed normalized_rule_finishes

theorem original_redex_has_a_closed_solution :
    ∃ solution : empty Tower.rules ⟶ frame, (frames setting.levels).Models solution [equation left right] := by
  refine ⟨eqToHom normalized_rule_has_empty_target.symm ≫ (run 24).answer, ?_⟩
  exact Frames.models_comp (X := frames setting.levels) original_redex_equation_has_principal_answer.sound
    (eqToHom normalized_rule_has_empty_target.symm)

theorem zero_budget_preserves_original_redex :
    (⟨(run 0).target, (run 0).remaining⟩ : (Γ : Context Tower.rules) × EquationStore (TotalTerm Γ)) =
      ⟨frame, [equation left right]⟩ := by rfl'

/-- A partial reduction provider may leave lambda values opaque. Direct
typed recovery must not acquire a new normalization requirement. -/
def opaqueLambdas : ExecutableReduction.Reducer Tower.rules := fun fuel _ term =>
  match term with
  | .lam _ => none
  | other => ConversionControls.reducer fuel other

def identityRight : Term frame viewedType :=
  ContextualDependentCheckingBoundary.identity.reindex (projectionHom _ type)

theorem normalized_route_is_unfinished_on_opaque_value (fuel : Nat) :
    ContextualDependentProjectionInversion.recover (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
      TowerModel.algebra Controls.declarations_formed ExecutableTowerChoices.choices opaqueLambdas fuel
      (withoutNewest (empty Tower.rules) type) (𝟙 frame) (𝟙 frame) type
      (⟨viewedType, identityRight⟩ : TotalTerm frame) = none := by rfl'

def opaqueRun := stepNewest (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads
  TowerModel.algebra Controls.declarations_formed ExecutableTowerChoices.choices opaqueLambdas
  24 left identityRight []

theorem direct_route_still_finishes : opaqueRun.remaining = [] := by decide +kernel

theorem direct_route_still_principal :
    (frames setting.levels).Principal [equation left identityRight] opaqueRun.answer :=
  opaqueRun.completed direct_route_still_finishes

end ContextualDependentFlex.NormalizedControls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
