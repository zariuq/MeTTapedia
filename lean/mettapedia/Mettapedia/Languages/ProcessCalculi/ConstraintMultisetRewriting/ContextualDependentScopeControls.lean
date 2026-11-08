import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentScope
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexWakeup

/-!
# Scoped patterns and the rigid-variable boundary

Closing the actual pattern F x = G x computes the lambda equation consumed
by the existing solver. Its principal answer factors all scoped solutions.
In contrast, x = Ground is solvable when x is a metavariable, but has no
solution when x is a local binder: identity and a constant function differ.
Nested dependent binders also close without a closed inhabitant requirement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentScope.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentEta ContextualDependentUpdate ContextualDependentFlex

abbrev setting := ConversionControls.setting

def patternDomain : TypeOver ContextualDependentFlex.Controls.frame :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

def patternCodomain : TypeOver (extend ContextualDependentFlex.Controls.frame patternDomain) :=
  ⟨.head (.sort Tower.zero), .sort (.succ Tower.zero), .sort _, .headType (.sort _)⟩

def patternBody : Active (extend ContextualDependentFlex.Controls.frame patternDomain) :=
  ⟨patternCodomain,
    ⟨.app (.var 1) (.var 0), Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero)) (B := .head (.sort Tower.zero))
      (.var 1) (.var 0)⟩,
    ⟨.app (.var 2) (.var 0), Derivable.appElim (R := Tower.rules) (A := .head (.sort Tower.zero)) (B := .head (.sort Tower.zero))
      (.var 2) (.var 0)⟩⟩

def pattern : Scoped ContextualDependentFlex.Controls.frame := .bind patternDomain (.active patternBody)

def closedPattern : Active ContextualDependentFlex.Controls.frame :=
  ⟨ContextualDependentFlex.Controls.viewedType,
    ContextualDependentFlex.Controls.left, ContextualDependentFlex.Controls.right⟩

theorem pattern_closes_to_solver_input :
    pattern.closeWith setting.levels ExecutableTowerChoices.choices = some closedPattern := by rfl'

theorem scoped_pattern_solved : pattern.Holds (ContextualDependentFlex.Controls.run 16 []).answer := by
  apply (Scoped.closeWith_holds_iff setting.levels ExecutableTowerChoices.choices
    pattern pattern_closes_to_solver_input _).mp
  exact (Active.holds_iff_models setting.levels closedPattern _).mpr
    ContextualDependentFlex.Controls.actual_pattern_principal.sound

theorem every_scoped_pattern_solution_factors {Δ : Context Tower.rules}
    (solution : Δ ⟶ ContextualDependentFlex.Controls.frame) (solved : pattern.Holds solution) :
    ∃ residual : Δ ⟶ (ContextualDependentFlex.Controls.run 16 []).target,
      ∀ term : TotalTerm ContextualDependentFlex.Controls.frame,
        (frames setting.levels).E (term.reindex solution)
          (term.reindex (residual ≫ (ContextualDependentFlex.Controls.run 16 []).answer)) := by
  have active := (Scoped.closeWith_holds_iff setting.levels ExecutableTowerChoices.choices
    pattern pattern_closes_to_solver_input solution).mpr solved
  exact ContextualDependentFlex.Controls.actual_pattern_principal.factors Δ solution
    ((Active.holds_iff_models setting.levels closedPattern solution).mp active)

def mismatch : Active Wakeup.frame := ⟨Wakeup.viewedUniverse, Wakeup.unknownType, Wakeup.ground⟩
def rigid : Scoped (empty Tower.rules) := .bind Wakeup.universeType (.active mismatch)
def groundValue : Term (empty Tower.rules) Wakeup.universeType :=
  ⟨.head .legacyGround, .headType .legacyGround⟩

theorem flexible_has_closed_solution :
    ∃ solution : empty Tower.rules ⟶ Wakeup.frame,
      (frames setting.levels).Models solution [mismatch.equation] := by
  refine ⟨Elimination.instantiate (empty Tower.rules) groundValue,
    (Active.holds_iff_models setting.levels mismatch _).mp ?_⟩
  exact Derivable.refl groundValue.typed

theorem rigid_has_no_solution {Δ : Context Tower.rules} (solution : Δ ⟶ empty Tower.rules) :
    ¬ rigid.Holds solution := by
  intro same
  have typedEquality : TypeEq Tower.rules (extend Δ (Wakeup.universeType.reindex solution)).raw
      (.var 0) (.head .legacyGround) :=
    ⟨.sort Tower.zero, .sort _, same⟩
  have neutral := TypeEq.neutral_form TowerModel.facts typedEquality
    (extend Δ (Wakeup.universeType.reindex solution)).formed (.var 0) (.inl ⟨.legacyGround, rfl⟩)
  exact neutral.not_former.1 .legacyGround rfl

def rigidFunctions : Active (empty Tower.rules) :=
  ⟨Examples.TypedContextualControls.functionType,
    ⟨.lam (.var 0), .lamIntro Examples.TypedContextualControls.functionType.formed
      Examples.TypedContextualControls.functionType.universeWitness (.var 0)⟩,
    ⟨.lam (.head .legacyGround), .lamIntro Examples.TypedContextualControls.functionType.formed
      Examples.TypedContextualControls.functionType.universeWitness (.headType .legacyGround)⟩⟩

theorem rigid_closes_to_unequal_functions :
    rigid.closeWith setting.levels ExecutableTowerChoices.choices = some rigidFunctions := by rfl'

theorem identity_and_constant_are_not_unifiable :
    ¬ (frames setting.levels).Solvable [rigidFunctions.equation] := by
  rintro ⟨Δ, solution, solved⟩
  exact rigid_has_no_solution solution
    ((Scoped.closeWith_holds_iff setting.levels ExecutableTowerChoices.choices
      rigid rigid_closes_to_unequal_functions solution).mp
        ((Active.holds_iff_models setting.levels rigidFunctions solution).mpr solved))

def dependentDomain : TypeOver Wakeup.frame :=
  ⟨.var 0, .sort Tower.zero, .sort _, .var 0⟩
def dependentValueType : TypeOver (extend Wakeup.frame dependentDomain) :=
  dependentDomain.reindex (projectionHom _ dependentDomain)
def dependentBody : Active (extend Wakeup.frame dependentDomain) :=
  ⟨dependentValueType, ⟨.var 0, .var 0⟩, ⟨.var 0, .var 0⟩⟩
def nested : Scoped (empty Tower.rules) :=
  .bind Wakeup.universeType (.bind dependentDomain (.active dependentBody))

theorem nested_dependent_binders_hold {Δ : Context Tower.rules} (solution : Δ ⟶ empty Tower.rules) :
    nested.Holds solution :=
  Derivable.refl (dependentBody.left.typed.substitute
    (rawLift (rawLift solution Wakeup.universeType) dependentDomain).typed)

theorem tower_closing_terminates {Γ : Context Tower.rules} (constraint : Scoped Γ) :
    ∃ closed, constraint.closeWith setting.levels ExecutableTowerChoices.choices = some closed := by
  apply Scoped.closeWith_exists
  intro first second firstUniverse secondUniverse
  cases firstUniverse
  cases secondUniverse
  exact ⟨_, rfl⟩

theorem nested_has_closed_solution :
    ∃ closed, nested.closeWith setting.levels ExecutableTowerChoices.choices = some closed ∧
      (frames setting.levels).Models (𝟙 (empty Tower.rules)) [closed.equation] := by
  obtain ⟨closed, computed⟩ := tower_closing_terminates nested
  exact ⟨closed, computed, (Active.holds_iff_models setting.levels closed _).mp
    ((Scoped.closeWith_holds_iff setting.levels ExecutableTowerChoices.choices nested computed _).mpr
      (nested_dependent_binders_hold _))⟩

end ContextualDependentScope.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
