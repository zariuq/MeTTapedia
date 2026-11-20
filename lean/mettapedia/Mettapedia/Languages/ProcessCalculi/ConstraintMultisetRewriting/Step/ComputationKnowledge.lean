import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationExecution

/-!
# Pure computational runs survive consistent knowledge changes

The resource operation only matches the selected row with itself. Replacing
the initial knowledge by any solvable store therefore preserves the complete
instruction sequence, values and occurrence choices. The actual new knowledge
is retained; it is not silently erased or equated with the old store.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicParallel NativeTypesOnTheStep.Computing

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  {qualified : Qualified S} {presentation : SchemaPresentation S.R}

def Configuration.renew (configuration : Configuration (S := S))
    (knowledge : EquationStore (TotalTerm configuration.state.frame))
    (consistent : (frames S.levels).Solvable knowledge) : Configuration (S := S) :=
  ⟨{configuration.state with knowledge := knowledge}, configuration.active, configuration.present, consistent⟩

def Instruction.renew {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration)
    (knowledge : EquationStore (TotalTerm configuration.state.frame))
    (consistent : (frames S.levels).Solvable knowledge) :
    Instruction presentation (configuration.renew knowledge consistent) := ⟨instruction.event, instruction.source⟩

def Configuration.visible (configuration : Configuration (S := S)) : State S.R Nat :=
  {configuration.state with knowledge := []}

theorem Instruction.renew_next {configuration : Configuration (S := S)}
    (instruction : Instruction presentation configuration)
    (knowledge : EquationStore (TotalTerm configuration.state.frame))
    (consistent : (frames S.levels).Solvable knowledge) (target : Nat)
    (fresh : target ∉ configuration.state.present) :
    (instruction.renew knowledge consistent).next qualified target fresh =
      (instruction.next qualified target fresh).renew
        ((instruction.renew knowledge consistent).next qualified target fresh).state.knowledge
        ((instruction.renew knowledge consistent).next qualified target fresh).consistent := rfl

def Execution.renew : ∀ {configuration : Configuration (S := S)}
    (_execution : Execution qualified presentation configuration)
    (knowledge : EquationStore (TotalTerm configuration.state.frame))
    (consistent : (frames S.levels).Solvable knowledge),
      Execution qualified presentation (configuration.renew knowledge consistent)
  | _, .nil configuration, knowledge, consistent => .nil (configuration.renew knowledge consistent)
  | _, .cons instruction target fresh rest, knowledge, consistent =>
      let renewed := (instruction.renew knowledge consistent).next qualified target fresh
      .cons (instruction.renew knowledge consistent) target fresh
        ((instruction.renew_next knowledge consistent target fresh).symm ▸
          rest.renew renewed.state.knowledge renewed.consistent)

theorem Execution.term_cast {before after : Configuration (S := S)} (same : before = after)
    (execution : Execution qualified presentation before) : HEq (same ▸ execution).term execution.term := by
  cases same
  rfl

theorem Execution.visible_cast {before after : Configuration (S := S)} (same : before = after)
    (execution : Execution qualified presentation before) : (same ▸ execution).last.visible = execution.last.visible := by
  cases same
  rfl

theorem Execution.renew_term {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration)
    (knowledge : EquationStore (TotalTerm configuration.state.frame))
    (consistent : (frames S.levels).Solvable knowledge) :
    (execution.renew knowledge consistent).term = execution.term := by
  induction execution with
  | nil => rfl
  | cons instruction target fresh rest ih =>
      change ((instruction.renew_next knowledge consistent target fresh).symm ▸
        rest.renew _ _).term = rest.term
      let next := (instruction.renew knowledge consistent).next qualified target fresh
      have same := Execution.term_cast (instruction.renew_next knowledge consistent target fresh).symm
        (rest.renew next.state.knowledge next.consistent)
      exact eq_of_heq (same.trans (heq_of_eq (ih next.state.knowledge next.consistent)))

theorem Execution.renew_visible {configuration : Configuration (S := S)}
    (execution : Execution qualified presentation configuration)
    (knowledge : EquationStore (TotalTerm configuration.state.frame))
    (consistent : (frames S.levels).Solvable knowledge) :
    (execution.renew knowledge consistent).last.visible = execution.last.visible := by
  induction execution with
  | nil => rfl
  | cons instruction target fresh rest ih =>
      change ((instruction.renew_next knowledge consistent target fresh).symm ▸
        rest.renew _ _).last.visible = rest.last.visible
      let next := (instruction.renew knowledge consistent).next qualified target fresh
      have same := Execution.visible_cast (instruction.renew_next knowledge consistent target fresh).symm
        (rest.renew next.state.knowledge next.consistent)
      exact same.trans (ih next.state.knowledge next.consistent)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Execution.renew_term
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.Execution.renew_visible
