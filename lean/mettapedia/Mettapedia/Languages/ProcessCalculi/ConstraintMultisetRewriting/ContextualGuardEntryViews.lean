import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProductionAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRegression
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceViews

/-!
# Source-prefix guards become observations of entry rows and compiled changes

The finite view bank contains initial schema variables and separately scoped
production origins. Entry physical names retain the initial row. Created
names select compiled origins. All comparisons need only shapes and resource
executability, so guard-success assumptions do not enter their compilation.

The regression accepts a further capture assignment and arbitrary information
at the observed cut. A current event can therefore contribute its own port
equations without replacing the original occurrence world by a later one.
Native guard-expression admission and the complete binding-problem embedding
remain separate from these constructed observation formulas.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows ContextualConditionalGuards
open ContextualConjunctiveQueries
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last Next Later : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    {next : Next → MetaArity S} {later : Later → MetaArity S}

def entryVariables (schedule : Schedule S O Γ sort before after) : Option O → Type :=
  ContextualOccurrenceViews.Variables (First := First) after.declarations schedule.origins

def entryDeclarations (schedule : Schedule S O Γ sort before after) :
    ∀ index, schedule.entryVariables index → MetaArity S :=
  ContextualOccurrenceViews.declarations first after.declarations schedule.origins

abbrev entryBank (schedule : Schedule S O Γ sort before after) :=
  ContextualConditionalRowPacking.family schedule.entryVariables schedule.entryDeclarations

def inputRow (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Row schedule.entryBank after.declarations Γ sort :=
  ContextualOccurrenceViews.inputRow first before.declarations after.declarations schedule.origins
    before.rows schedule.frame.assignment occurrence

def creationRow (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Row schedule.entryBank after.declarations Γ sort :=
  ContextualOccurrenceViews.creationRow first after.declarations schedule.origins occurrence

def physicalRows (schedule : Schedule S O Γ sort before after) :
    OccurrenceAllocationRenaming.Name O → Row schedule.entryBank after.declarations Γ sort :=
  ContextualOccurrenceViews.physicalRows first before.declarations after.declarations schedule.origins
    before.rows schedule.frame.assignment

def inputRows (schedule : Schedule S O Γ sort before after) (physical : OccurrenceAllocationRenaming.Name O) :
    Row schedule.entryBank after.declarations Γ sort := schedule.inputRow (OccurrenceAllocationRenaming.erase physical)

theorem input_row_instances (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches schedule.entryBank after.declarations candidate pattern (schedule.inputRow occurrence) ↔
      Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment) pattern (before.rows occurrence) :=
  ContextualOccurrenceViews.input_matches first before.declarations after.declarations schedule.origins
    before.rows schedule.frame.assignment occurrence candidate pattern

theorem creation_row_instances (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches schedule.entryBank after.declarations candidate pattern (schedule.creationRow occurrence) ↔
      Matches last after.declarations candidate pattern (after.rows occurrence) :=
  (ContextualOccurrenceViews.creation_matches first after.declarations schedule.origins occurrence candidate pattern).trans
    (schedule.origins_instances_of_shapes shapes next candidate pattern occurrence)

/-- Initial and created physical identities have the exact row meaning of the source prefix. -/
theorem physical_row_instances (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches schedule.entryBank after.declarations candidate pattern
      (schedule.physicalRows
        ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)) ↔
      Matches last after.declarations candidate pattern (after.rows occurrence) := by
  let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections
  have represented := ContextualOccurrenceViews.physical_instances first before.declarations after.declarations schedule.origins
    before.rows schedule.frame.assignment cursor.current cursor.projects
    (fun original inherited => by
      have missing := (schedule.current_name_inherited_iff_shapes shapes original).mp inherited
      have origin := schedule.production_origin original
      simpa only [productionOrigin, missing, Option.map_none, Option.getD_none] using origin.symm)
    occurrence candidate pattern
  exact represented.trans (schedule.origins_instances_of_shapes shapes next candidate pattern occurrence)

theorem prefix_net_enabled (schedule : Schedule S O Γ sort before after)
    (resources : Executable unitLabel before.present schedule.commits) :
    Enabled OccurrenceAllocationRenaming.label (before.present.image Sum.inl) schedule.net.effect := by
  have executable := (schedule.allocated_resources_of_executable resources).1
  exact ((CompiledSchedule.compile_correct OccurrenceAllocationRenaming.label
    (OccurrenceAllocationRenaming.commits schedule.allocated) (before.present.image Sum.inl)).2
    ((CompiledSchedule.compile_condition_iff _ _ _).mpr executable)).1

/-- A further capture frame admits the current event's own equations and pattern variables. -/
theorem prefix_guard_iff (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits) (change : Assignment after.declarations later)
    (candidate : Assignment later next) (check : Check (Term (signature S later) Γ sort)) :
    Holds last candidate (fun occurrence => (after.rows occurrence).map last after.declarations change) after.present check ↔
      ContextualGuardRegression.entryCondition schedule.entryBank schedule.entryBank candidate
        (fun physical => (schedule.inputRows physical).map schedule.entryBank after.declarations change)
        (fun physical => (schedule.physicalRows physical).map schedule.entryBank after.declarations change)
        (before.present.image Sum.inl) schedule.net.effect.taken schedule.net.effect.made check := by
  let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections
  have image := ContextualGuardRegression.holds_image_of_matches last schedule.entryBank cursor.current cursor.injective candidate
    (fun occurrence => (after.rows occurrence).map last after.declarations change)
    (fun physical => (schedule.physicalRows physical).map schedule.entryBank after.declarations change) after.present
    (fun pattern occurrence _member => by
      rw [matches_map_iff, matches_map_iff]
      exact (schedule.physical_row_instances shapes occurrence next (Assignment.compose candidate change)
        (instantiate candidate pattern)).symm) check
  have world := schedule.assembled_physical_of_resources resources
  change fire (before.present.image Sum.inl) schedule.net.effect = after.present.image cursor.current at world
  rw [← world] at image
  have enabled := schedule.prefix_net_enabled resources
  apply image.symm.trans
  exact ContextualGuardRegression.holds_after_iff schedule.entryBank schedule.entryBank candidate
    (fun physical => (schedule.inputRows physical).map schedule.entryBank after.declarations change)
    (fun physical => (schedule.physicalRows physical).map schedule.entryBank after.declarations change)
    (before.present.image Sum.inl) schedule.net.effect.taken schedule.net.effect.made check
    enabled.taken_subset enabled.fresh (by
      intro pattern physical member _outside
      obtain ⟨occurrence, _present, rfl⟩ := Finset.mem_image.mp member
      rfl)

/-- Original-cut information is quantified unchanged; no successful guard is assumed. -/
theorem prefix_ask_iff (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (resources : Executable unitLabel before.present schedule.commits) (change : Assignment after.declarations later)
    (problem : ContextualResidual.Problem later) (check : Check (Term (signature S later) Γ sort)) :
    Ask last problem (fun occurrence => (after.rows occurrence).map last after.declarations change) after.present check ↔
      ∀ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment later future),
        ContextualResidual.Models candidate problem →
          ContextualGuardRegression.entryCondition schedule.entryBank schedule.entryBank candidate
            (fun physical => (schedule.inputRows physical).map schedule.entryBank after.declarations change)
            (fun physical => (schedule.physicalRows physical).map schedule.entryBank after.declarations change)
            (before.present.image Sum.inl) schedule.net.effect.taken schedule.net.effect.made check := by
  constructor <;> intro observed Future future candidate model
  · exact (schedule.prefix_guard_iff shapes resources change candidate check).mp (observed Future future candidate model)
  · exact (schedule.prefix_guard_iff shapes resources change candidate check).mpr (observed Future future candidate model)

def ownEntryCondition {Query : Type} (schedule : Schedule S O Γ sort before after) (queries : Query → MetaArity S)
    (check : Check (Term (signature S (queryFamily queries after.declarations)) Γ sort))
    {Future : Type} (future : Future → MetaArity S)
    (candidate : Assignment (family queries last after.declarations) future) : Prop :=
  ContextualGuardRegression.entryCondition schedule.entryBank schedule.entryBank candidate
    (fun physical => (schedule.inputRows physical).map schedule.entryBank after.declarations
      (captureEmbedding queries last after.declarations))
    (fun physical => (schedule.physicalRows physical).map schedule.entryBank after.declarations
      (captureEmbedding queries last after.declarations))
    (before.present.image Sum.inl) schedule.net.effect.taken schedule.net.effect.made
    (check.map (queryView queries last after.declarations))

/-- The actual current clause contributes its own port/tell equations at the saved guard cut. -/
theorem original_cut_entry_iff {Query : Type} (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (resources : Executable unitLabel before.present schedule.commits)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries after.declarations)) Γ sort))
    (picked : Selection O) :
    (originalCut after queries plan picked).Holds ↔
      ∀ check ∈ plan.rule.checks, ∀ (Future : Type) (future : Future → MetaArity S)
        (candidate : Assignment (family queries last after.declarations) future),
        ContextualResidual.Models candidate (ContextualClauseSourceState.information queries last after plan picked) →
          schedule.ownEntryCondition queries check future candidate := by
  simp only [Cut.Holds, originalCut, List.forall_mem_map]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  exact schedule.prefix_ask_iff shapes resources (captureEmbedding queries last after.declarations)
    (ContextualClauseSourceState.information queries last after plan picked)
    (check.map (queryView queries last after.declarations))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
