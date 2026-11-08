import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleOrigins
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRowPacking
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleAllocation

/-!
# Assembling computed row origins into one conditional row-store format

Origins produce actual conditional row data with their own private families.
Packing gives them a common private bank without changing captured names or
combining independent schema conditions. Information and physical presence
come from the compiled deltas and net update, not the final source rows.

This constructs and compares the publication data. Realizing the entire
assembled store by the selected ordinary native firing profile remains a
separate theorem; this module does not define an evaluator-backed step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {V Next O : Type} {declaration : V → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}

def Origin.Private : Origin declaration Γ sort → Type
  | .retained (Local := Local) _ _ _ _ => Local
  | .schema (Saved := Saved) _ _ _ => Saved
  | .shared _ => Empty

def Origin.privateDecl (origin : Origin declaration Γ sort) : origin.Private → MetaArity S :=
  match origin with
  | .retained locals _ _ _ => locals
  | .schema saved _ _ => saved
  | .shared _ => fun name => nomatch name

def Origin.asRow (origin : Origin declaration Γ sort) : Row origin.privateDecl declaration Γ sort :=
  match origin with
  | .retained locals saved row transport => row.map locals saved transport
  | .schema saved problem value => ContextualConditionalPublication.store saved declaration ⟨problem, value⟩
  | .shared value => ofStored _ _ (.shared value)

theorem Origin.asRow_instances (origin : Origin declaration Γ sort) (candidate : Assignment declaration next)
    (pattern : Term (signature S next) Γ sort) :
    Matches origin.privateDecl declaration candidate pattern origin.asRow ↔ origin.Instances candidate pattern := by
  cases origin with
  | retained locals saved row transport => exact matches_map_iff locals _ transport candidate pattern row
  | schema saved problem value =>
      exact ContextualConditionalPublication.store_matches_iff saved declaration candidate ⟨problem, value⟩ pattern
  | shared value =>
      rw [Origin.asRow, ofStored_matches_iff, ContextualGuardMatching.shared_matches_iff]
      rfl

namespace Schedule

variable [DecidableEq O] {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

abbrev rowVariables (schedule : Schedule S O Γ sort before after) (occurrence : O) :=
  (schedule.origins occurrence).Private
abbrev rowDeclarations (schedule : Schedule S O Γ sort before after) (occurrence : O) :=
  (schedule.origins occurrence).privateDecl
abbrev rowFamily (schedule : Schedule S O Γ sort before after) :=
  ContextualConditionalRowPacking.family schedule.rowVariables schedule.rowDeclarations

def assembledRow (schedule : Schedule S O Γ sort before after) (physical : OccurrenceAllocationRenaming.Name O) :
    Row schedule.rowFamily after.declarations Γ sort :=
  ContextualConditionalRowPacking.pack schedule.rowVariables schedule.rowDeclarations after.declarations
    (OccurrenceAllocationRenaming.erase physical) (schedule.origins (OccurrenceAllocationRenaming.erase physical)).asRow

def net (schedule : Schedule S O Γ sort before after) : CompiledSchedule (OccurrenceAllocationRenaming.Name O) Unit :=
  CompiledSchedule.compile OccurrenceAllocationRenaming.label (OccurrenceAllocationRenaming.commits schedule.allocated)

abbrev assembled (schedule : Schedule S O Γ sort before after) :
    ContextualClauseSourceState.World schedule.rowFamily (OccurrenceAllocationRenaming.Name O) Γ sort where
  Names := after.Names
  equality := after.equality
  declarations := after.declarations
  equations := schedule.compile.problem
  present := fire (before.present.image Sum.inl) schedule.net.effect
  rows := schedule.assembledRow

theorem assembled_information (schedule : Schedule S O Γ sort before after) :
    schedule.assembled.equations = after.equations := schedule.final_equations.symm

theorem assembled_physical_of_resources (schedule : Schedule S O Γ sort before after)
    (resources : Executable unitLabel before.present schedule.commits) :
    schedule.assembled.present =
      after.present.image (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current := by
  have executable := (schedule.allocated_resources_of_executable resources).1
  change fire _ (CompiledSchedule.compile _ _).effect = _
  rw [CompiledSchedule.compile_effect executable]
  exact (schedule.allocated_resources_of_executable resources).2

theorem assembled_physical (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) :
    schedule.assembled.present =
      after.present.image (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current :=
  schedule.assembled_physical_of_resources
    (schedule.admitted_characterization.mp (schedule.compile_exact.mp accepted)).2.1

/-- Every assembled row has exactly the source row's conditional instances in all later families. -/
theorem assembled_row_instances_of_shapes (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (occurrence : O)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches schedule.rowFamily after.declarations candidate pattern
      (schedule.assembled.rows
        ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)) ↔
      Matches last after.declarations candidate pattern (after.rows occurrence) := by
  change Matches _ _ candidate pattern (ContextualConditionalRowPacking.pack _ _ _ _ _) ↔ _
  rw [(OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).projects]
  exact (ContextualConditionalRowPacking.matches_iff schedule.rowVariables schedule.rowDeclarations after.declarations
    occurrence (schedule.origins occurrence).asRow candidate pattern).trans
      (((schedule.origins occurrence).asRow_instances candidate pattern).trans
        (schedule.origins_instances_of_shapes shapes next candidate pattern occurrence))

theorem assembled_row_instances (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) (occurrence : O)
    {Next : Type} (next : Next → MetaArity S) (candidate : Assignment after.declarations next)
    (pattern : Term (signature S next) Γ sort) :
    Matches schedule.rowFamily after.declarations candidate pattern
      (schedule.assembled.rows
        ((OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial schedule.selections).current occurrence)) ↔
      Matches last after.declarations candidate pattern (after.rows occurrence) :=
  schedule.assembled_row_instances_of_shapes
    (schedule.admitted_characterization.mp (schedule.compile_exact.mp accepted)).1 occurrence next candidate pattern

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
