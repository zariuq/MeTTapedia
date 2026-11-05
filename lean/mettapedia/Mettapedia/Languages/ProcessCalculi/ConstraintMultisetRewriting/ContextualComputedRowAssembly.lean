import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleRowAssembly

/-!
# Actual bounded solving for the assembled private-body result

The result combines an actual worklist return with the compiled row payloads
and one existing occurrence resource update. Original prefix conditions stay
inside their own rows. The current caller information retains the complete
compiled problem, including when the solver leaves a residual queue.

This is a solver-backed result construction. It does not identify that
construction with an ordinary single-clause native firing; that lowering
obligation remains explicit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

structure ComputedAssembly (schedule : Schedule S O Γ sort before after) (fuel : Nat) where
  accepted : schedule.compile.Holds before.present
  update : ContextualFrameUpdate.Update schedule.compile.problem
  computed : letI := after.equality
    ContextualFrameWorklist.run fuel after.declarations schedule.compile.problem = .residual update

theorem compute_assembly (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) (fuel : Nat) : Nonempty (ComputedAssembly schedule fuel) := by
  let _ := after.equality
  cases computed : ContextualFrameWorklist.run fuel after.declarations schedule.compile.problem with
  | refuted impossible =>
      obtain ⟨Future, future, candidate, model⟩ := accepted.2.2.1
      exact False.elim (impossible future candidate model)
  | residual update => exact ⟨⟨accepted, update, computed⟩⟩

namespace ComputedAssembly

variable {schedule : Schedule S O Γ sort before after} {fuel : Nat} (result : ComputedAssembly schedule fuel)

abbrev family := ContextualComputedFreshFrame.active after.declarations result.update.declaration

abbrev world : ContextualClauseSourceState.World schedule.rowFamily (OccurrenceAllocationRenaming.Name O) Γ sort where
  Names := after.Names ⊕ (result.update.Variables ⊕ Empty)
  equality := by let _ := after.equality; let _ := result.update.equality; infer_instance
  declarations := result.family
  equations := ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource result.update) schedule.compile.problem
  present := schedule.assembled.present
  rows physical := (schedule.assembledRow physical).map schedule.rowFamily after.declarations
    (ContextualComputedFreshFrame.includeSource result.update)

/-- An admitted computation can be unfinished, but its retained queue still has a model. -/
theorem residual_solvable : ContextualConditionalExecution.Solvable result.update.remaining := by
  obtain ⟨Future, future, candidate, model⟩ := result.accepted.2.2.1
  obtain ⟨residual, conditions, _projection⟩ := result.update.factors future candidate model
  exact ⟨Future, future, residual, conditions⟩

theorem physical_result : result.world.present =
    after.present.image (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current :=
  schedule.assembled_physical result.accepted

theorem enabled_net_update (result : ComputedAssembly schedule fuel) : Enabled OccurrenceAllocationRenaming.label
    (before.present.image Sum.inl) schedule.net.effect :=
  (schedule.allocated_net_commit result.accepted).1

/-- Original caller models are retained, independently of the worklist's completion status. -/
theorem information_iff {Next : Type} (next : Next → MetaArity S) (candidate : Assignment result.family next) :
    ContextualResidual.Models candidate result.world.equations ↔
      ContextualResidual.Models (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource result.update))
        after.equations := by
  change ContextualResidual.Models candidate (ContextualResidual.mapProblem _ schedule.compile.problem) ↔ _
  rw [ContextualResidual.models_mapProblem, ← schedule.assembled_information]

/-- The actual computed result keeps every source row's conditional instances at its allocated name. -/
theorem row_instances (occurrence : O) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment result.family next) (pattern : Term (signature S next) Γ sort) :
    Matches schedule.rowFamily result.family candidate pattern
      (result.world.rows
        ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)) ↔
    Matches last after.declarations
      (Assignment.compose candidate (ContextualComputedFreshFrame.includeSource result.update)) pattern (after.rows occurrence) := by
  change Matches _ _ candidate pattern (Row.map _ _ _ _) ↔ _
  rw [matches_map_iff]
  exact schedule.assembled_row_instances result.accepted occurrence next _ pattern

/-- Returned contextual values retain exactly their original conditional instances. -/
theorem value_instances (value : Term (signature S after.declarations) Γ sort)
    {Next : Type} (next : Next → MetaArity S) (pattern : Term (signature S next) Γ sort) :
    ContextualPublication.SourceInstances result.world.equations
      (instantiate (ContextualComputedFreshFrame.includeSource result.update) value) next pattern ↔
      ContextualPublication.SourceInstances after.equations value next pattern := by
  have transported := ContextualConditionalNaturality.source_instances_extension
    (ContextualComputedFreshFrame.declarationExtension result.update) schedule.compile.problem value next pattern
  rw [ContextualComputedFreshFrame.declarationExtension_assignment] at transported
  change ContextualPublication.SourceInstances
    (ContextualResidual.mapProblem (ContextualComputedFreshFrame.includeSource result.update) schedule.compile.problem)
    (instantiate (ContextualComputedFreshFrame.includeSource result.update) value) next pattern ↔ _
  rw [← schedule.assembled_information]
  exact transported

end ComputedAssembly

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
