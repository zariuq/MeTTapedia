import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentDispatch
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFlexWakeup
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalizationControls

/-!
# Queue selection, orientation, and heterogeneous wake-up controls

The defining equation is behind an initially heterogeneous obligation and
has its variable on the right. The computed dispatcher finds it, solves it,
and revisits the earlier obligation. Separate controls retain an unrelated
equation, a solvable non-pattern, and the whole store at zero budget.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentDispatch.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate

abbrev setting := ConversionControls.setting

def run {Γ : Context Tower.rules} (fuel : Nat) (type : TypeOver Γ)
    (problem : EquationStore (TotalTerm (extend Γ type))) :=
  step (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer fuel type problem

open ContextualDependentFlex.Wakeup in
def reversedDefinition : Equation (TotalTerm frame) := ContextualDependentFlex.equation ground unknownType

open ContextualDependentFlex.Wakeup in
def waitingFirst : EquationStore (TotalTerm frame) := [pending, reversedDefinition]

def awakened := run 24 ContextualDependentFlex.Wakeup.universeType waitingFirst

theorem later_reversed_definition_wakes_earlier_equation : awakened.remaining = [] := by rfl'

theorem declaration_is_removed : awakened.target = empty Tower.rules := by rfl'

theorem assignment_is_computed : awakened.answer.substitution 0 = .head .legacyGround := by rfl'

theorem whole_original_queue_has_principal_answer :
    (frames setting.levels).Principal waitingFirst awakened.answer :=
  awakened.completed later_reversed_definition_wakes_earlier_equation

theorem actual_closed_solution :
    ∃ solution : empty Tower.rules ⟶ ContextualDependentFlex.Wakeup.frame,
      (frames setting.levels).Models solution waitingFirst := by
  refine ⟨eqToHom declaration_is_removed.symm ≫ awakened.answer, ?_⟩
  exact Frames.models_comp (X := frames setting.levels) whole_original_queue_has_principal_answer.sound
    (eqToHom declaration_is_removed.symm)

theorem earlier_equation_alone_is_retained :
    (⟨(run 24 ContextualDependentFlex.Wakeup.universeType [ContextualDependentFlex.Wakeup.pending]).target,
      (run 24 ContextualDependentFlex.Wakeup.universeType [ContextualDependentFlex.Wakeup.pending]).remaining⟩ :
      (Γ : Context Tower.rules) × EquationStore (TotalTerm Γ)) =
        ⟨ContextualDependentFlex.Wakeup.frame, [ContextualDependentFlex.Wakeup.pending]⟩ := by rfl'

theorem zero_budget_retains_every_obligation :
    run 0 ContextualDependentFlex.Wakeup.universeType waitingFirst =
      Update.pending setting.levels waitingFirst :=
  step_zero TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentFlex.Controls.declarations_formed ExecutableTowerChoices.choices
    ConversionControls.reducer _ _

open ContextualDependentFlex.Controls in
def independentEarlier : EquationStore (TotalTerm frame) :=
  [sideCondition, ContextualDependentFlex.equation right left, sideCondition]

def partlySolved := run 24 ContextualDependentFlex.Controls.secondType independentEarlier

theorem unrelated_duplicates_survive : partlySolved.remaining.length = 2 := by rfl'

theorem selected_definition_really_eliminates : partlySolved.target = ContextualDependentFlex.Controls.base := by rfl'

open ContextualDependentFlex.Controls in
def recursiveProblem : EquationStore (TotalTerm frame) := [ContextualDependentFlex.equation left recursiveRight]

theorem solvable_nonpattern_is_not_rejected :
    (frames setting.levels).Solvable recursiveProblem ∧
    (⟨(run 24 ContextualDependentFlex.Controls.secondType recursiveProblem).target,
      (run 24 ContextualDependentFlex.Controls.secondType recursiveProblem).remaining⟩ :
      (Γ : Context Tower.rules) × EquationStore (TotalTerm Γ)) =
        ⟨ContextualDependentFlex.Controls.frame, recursiveProblem⟩ := by
  exact ⟨ContextualDependentFlex.Controls.recursive_nonpattern_has_a_solution, by rfl'⟩

namespace ConvertedAnnotations

abbrev type := ContextualDependentFlex.NormalizedControls.type
abbrev frame := ContextualDependentFlex.NormalizedControls.frame
def originalRight : TotalTerm frame :=
  TotalTerm.reindex ContextualDependentNormalization.Controls.original (projectionHom _ type)
def problem : EquationStore (TotalTerm frame) :=
  [(originalRight, ⟨_, ContextualDependentFlex.NormalizedControls.left⟩)]
def computed := run 24 type problem

theorem annotations_have_different_syntax :
    originalRight.1.code ≠ ContextualDependentFlex.NormalizedControls.viewedType.code := by
  decide +kernel

theorem conversion_and_reversal_finish : computed.remaining = [] := by rfl'

theorem recovered_value_is_identity : computed.answer.substitution 0 = .lam (.var 0) := by rfl'

theorem principal_for_original_annotations : (frames setting.levels).Principal problem computed.answer :=
  computed.completed conversion_and_reversal_finish

end ConvertedAnnotations
end ContextualDependentDispatch.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
