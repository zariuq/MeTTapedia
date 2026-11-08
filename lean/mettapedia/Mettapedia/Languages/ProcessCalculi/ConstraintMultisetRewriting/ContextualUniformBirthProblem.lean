import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualIndependentProblems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleBirthModels

/-!
# One actual solver update for independent creation conditions

The current caller problem occupies one declaration block. Every produced
descriptor has a separate block for its creation-time problem. An admitted
body supplies models for all of these blocks; dormant input-row conditions
are not added indiscriminately. The existing ordinary publication form can
therefore use the whole returned update without narrowing a birth value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows

namespace Schedule

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem admitted_final_solvable (schedule : Schedule S O Γ sort before after) :
    schedule.Admitted → ContextualConditionalExecution.Solvable after.equations := by
  cases schedule with
  | nil _ => exact id
  | snoc _ _ _ _ => exact fun admitted => admitted.2.solvable

abbrev BirthIndex (schedule : Schedule S O Γ sort before after) := Fin schedule.births.length
abbrev BlockIndex (schedule : Schedule S O Γ sort before after) := Option schedule.BirthIndex

def blockVariables (schedule : Schedule S O Γ sort before after) : schedule.BlockIndex → Type
  | none => after.Names
  | some index => (schedule.births.get index).SavedNames

def blockDeclarations (schedule : Schedule S O Γ sort before after) :
    ∀ index, schedule.blockVariables index → MetaArity S
  | none => after.declarations
  | some index => (schedule.births.get index).saved

def currentProblem (schedule : Schedule S O Γ sort before after) : ContextualResidual.Problem after.declarations :=
  ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas

def blockConditions (schedule : Schedule S O Γ sort before after) :
    ∀ index, ContextualResidual.Problem (schedule.blockDeclarations index)
  | none => schedule.currentProblem
  | some index => (schedule.births.get index).problem

def blockIndices (schedule : Schedule S O Γ sort before after) : List schedule.BlockIndex :=
  none :: (List.finRange schedule.births.length).map some

theorem block_list_complete (schedule : Schedule S O Γ sort before after) (index : schedule.BlockIndex) :
    index ∈ schedule.blockIndices := by
  cases index <;> simp [blockIndices]

abbrev uniformFamily (schedule : Schedule S O Γ sort before after) :=
  ContextualIndependentProblems.family schedule.blockVariables schedule.blockDeclarations

instance uniformEquality (schedule : Schedule S O Γ sort before after) :
    DecidableEq (ContextualAnswerFamilies.Names schedule.blockVariables) := by
  letI : ∀ index, DecidableEq (schedule.blockVariables index) := fun index =>
    match index with
    | none => after.equality
    | some index => (schedule.births.get index).equality
  infer_instance

def uniformProblem (schedule : Schedule S O Γ sort before after) : ContextualResidual.Problem schedule.uniformFamily :=
  ContextualIndependentProblems.problem schedule.blockVariables schedule.blockDeclarations schedule.blockConditions schedule.blockIndices

theorem blocks_solvable (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted)
    (index : schedule.BlockIndex) : ContextualConditionalExecution.Solvable (schedule.blockConditions index) := by
  cases index with
  | none =>
      change ContextualConditionalExecution.Solvable schedule.currentProblem
      change ContextualConditionalExecution.Solvable
        (ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas)
      rw [← schedule.final_equations]
      exact schedule.admitted_final_solvable admitted
  | some index =>
      exact schedule.births_solvable admitted _ (List.get_mem _ _)

theorem uniform_solvable (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted) :
    ContextualConditionalExecution.Solvable schedule.uniformProblem :=
  ContextualIndependentProblems.solvable schedule.blockVariables schedule.blockDeclarations schedule.blockConditions
    (schedule.blocks_solvable admitted) schedule.blockIndices

/-- Every given current caller model extends to the private birth blocks with its assignment fixed. -/
theorem current_model_extends (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next,
      ∃ combined : Assignment schedule.uniformFamily extension.declarations,
        ContextualResidual.Models combined schedule.uniformProblem ∧
        Assignment.compose combined
            (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations none) =
          Assignment.compose extension.assignment candidate := by
  have currentModel : ContextualResidual.Models candidate (schedule.blockConditions none) := by
    change ContextualResidual.Models candidate
      (ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas)
    rw [← schedule.final_equations]
    exact model
  exact ContextualIndependentProblems.extend_model schedule.blockVariables schedule.blockDeclarations schedule.blockConditions
    (schedule.blocks_solvable admitted) schedule.blockIndices none candidate currentModel

theorem uniform_birth_instances (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted)
    (index : schedule.BirthIndex) {Next : Type} (next : Next → MetaArity S)
    (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances schedule.uniformProblem
      (instantiate (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations (some index))
        (schedule.births.get index).value) next pattern ↔
      ContextualPublication.SourceInstances (schedule.births.get index).problem (schedule.births.get index).value next pattern :=
  ContextualIndependentProblems.instances_iff schedule.blockVariables schedule.blockDeclarations schedule.blockConditions
    (schedule.blocks_solvable admitted) schedule.blockIndices (some index) (schedule.block_list_complete _)
    (schedule.births.get index).value pattern

theorem uniform_current_instances (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted)
    (value : Term (signature S after.declarations) Γ sort) {Next : Type} (next : Next → MetaArity S)
    (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances schedule.uniformProblem
      (instantiate (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations none) value) next pattern ↔
      ContextualPublication.SourceInstances after.equations value next pattern := by
  have exactInstances := ContextualIndependentProblems.instances_iff
    schedule.blockVariables schedule.blockDeclarations schedule.blockConditions (schedule.blocks_solvable admitted)
    schedule.blockIndices none (schedule.block_list_complete none) value pattern
  change ContextualPublication.SourceInstances _ _ _ _ ↔ ContextualPublication.SourceInstances schedule.currentProblem value next pattern at exactInstances
  rw [currentProblem, ← schedule.final_equations] at exactInstances
  exact exactInstances

end Schedule

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

structure UniformComputed (schedule : Schedule S O Γ sort before after) (fuel : Nat) where
  admitted : schedule.Admitted
  update : ContextualFrameUpdate.Update schedule.uniformProblem
  computed : ContextualFrameWorklist.run fuel schedule.uniformFamily schedule.uniformProblem = .residual update

theorem compute_uniform (schedule : Schedule S O Γ sort before after) (admitted : schedule.Admitted) (fuel : Nat) :
    Nonempty (UniformComputed schedule fuel) := by
  cases computed : ContextualFrameWorklist.run fuel schedule.uniformFamily schedule.uniformProblem with
  | refuted impossible =>
      obtain ⟨Future, future, candidate, model⟩ := schedule.uniform_solvable admitted
      exact False.elim (impossible future candidate model)
  | residual update => exact ⟨⟨admitted, update, computed⟩⟩

namespace UniformComputed

variable {schedule : Schedule S O Γ sort before after} {fuel : Nat} (result : UniformComputed schedule fuel)

abbrev family := ContextualComputedFreshFrame.active schedule.uniformFamily result.update.declaration

def birthRow {Local : Type} (locals : Local → MetaArity S) (index : schedule.BirthIndex) :
    Row (ContextualPublication.privateFamily locals result.update.declaration) result.family Γ sort :=
  ContextualConditionalPublication.ordinary locals result.update.declaration result.family
    (ContextualConditionalAnswers.ofUpdate result.update
      (instantiate (ContextualIndependentProblems.inclusion schedule.blockVariables schedule.blockDeclarations (some index))
        (schedule.births.get index).value))

/-- The unchanged ordinary publication constructor and one actual update preserve every birth's instances. -/
theorem birth_row_instances {Local Next : Type} (locals : Local → MetaArity S) (index : schedule.BirthIndex)
    (next : Next → MetaArity S) (candidate : Assignment result.family next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualPublication.privateFamily locals result.update.declaration) result.family candidate pattern
      (result.birthRow locals index) ↔
      ContextualPublication.SourceInstances (schedule.births.get index).problem (schedule.births.get index).value next pattern :=
  (ContextualConditionalPublication.update_matches_source locals result.family result.update candidate _ pattern).trans
    (schedule.uniform_birth_instances result.admitted index next pattern)

end UniformComputed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
