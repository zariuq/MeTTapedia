import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceViews

/-!
# Mixed clause prefixes instantiate the shared occurrence view

Only authored origins and the entry capture transport are supplied here.
Packing, input matching and allocated-name interpretation are the common
construction used by ordinary/shared clauses. Guard truth is not an input.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

abbrev entryVariables (schedule : Schedule S O Γ sort before after) :=
  ContextualOccurrenceViews.Variables (First := First) after.declarations schedule.productionOrigin

abbrev entryDeclarations (schedule : Schedule S O Γ sort before after) :=
  ContextualOccurrenceViews.declarations first after.declarations schedule.productionOrigin

abbrev entryBank (schedule : Schedule S O Γ sort before after) :=
  ContextualOccurrenceViews.bank first after.declarations schedule.productionOrigin

def physicalRows (schedule : Schedule S O Γ sort before after) :
    OccurrenceAllocationRenaming.Name O → Row schedule.entryBank after.declarations Γ sort :=
  ContextualOccurrenceViews.physicalRows first before.declarations after.declarations schedule.productionOrigin
    before.rows schedule.frame.assignment

theorem input_row_instances (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches schedule.entryBank after.declarations candidate pattern (schedule.physicalRows (.inl occurrence)) ↔
      Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment) pattern (before.rows occurrence) :=
  ContextualOccurrenceViews.input_matches first before.declarations after.declarations schedule.productionOrigin
    before.rows schedule.frame.assignment occurrence candidate pattern

theorem physical_row_instances (schedule : Schedule S O Γ sort before after) (shapes : schedule.ShapesHold)
    (occurrence : O) (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches schedule.entryBank after.declarations candidate pattern
        (schedule.physicalRows
          ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)) ↔
      Matches last after.declarations candidate pattern (after.rows occurrence) := by
  let cursor := OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections
  have represented := ContextualOccurrenceViews.physical_instances first before.declarations after.declarations schedule.productionOrigin
    before.rows schedule.frame.assignment cursor.current cursor.projects
    (fun original inherited => by
      have missing := (schedule.current_name_inherited_iff_shapes shapes original).mp inherited
      simp only [productionOrigin, missing, Option.map_none, Option.getD_none]) occurrence candidate pattern
  exact represented.trans (schedule.production_origin_instances_of_shapes shapes next candidate pattern occurrence)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
