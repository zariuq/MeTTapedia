import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateEntryCuts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies

/-!
# Mixed bodies as compiled native bodies

Every surviving output has an unconstrained private declaration block; its
conditions remain in its saved row rather than becoming global obligations.
The body is computed from source syntax, entry information and cuts, before
admission or native execution. The guard problem, with independent blocks
for the current information and each saved guard cut, is the generic one of
`ContextualNativeBodies`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualSourceSchedules hiding Schedule Birth Plan
open ContextualConditionalRows

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem cuts_solvable_of_final (schedule : Schedule S O Γ sort before after) :
    ContextualConditionalExecution.Solvable after.equations →
      ∀ cut ∈ schedule.cuts, ContextualConditionalExecution.Solvable cut.problem := by
  induction schedule with
  | nil _ => intro _consistent cut member; cases member
  | segment past plain prior =>
      intro consistent cut member
      change cut ∈ past.cuts.map (Cut.map plain.frame.assignment) ++ plain.cuts at member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp earlier
        exact (ContextualConditionalNaturality.solvable_extension_iff plain.frame original.problem).mpr
          (prior (plain.source_solvable consistent) original oldMember)
      · exact plain.cuts_solvable_of_final consistent cut current
  | template mid past queries inners rule picked prior =>
      intro consistent cut member
      change cut ∈ past.cuts.map (Cut.map (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment) ++
        [originalCut mid (ContextualTemplateSource.Expanded queries inners)
          (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked] at member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp earlier
        exact (ContextualConditionalNaturality.solvable_extension_iff
          (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations) original.problem).mpr
          (prior ((Schedule.template mid (Schedule.nil mid) queries inners rule picked).source_solvable consistent)
            original oldMember)
      · have only := List.mem_singleton.mp current
        subst cut
        exact consistent

private def birthVariables : Option (Birth after.declarations O Γ sort) → Type
  | none => Empty
  | some birth => birth.PrivateNames

private def birthDeclarations : (selected : Option (Birth after.declarations O Γ sort)) →
    birthVariables selected → MetaArity S
  | none => fun impossible => nomatch impossible
  | some birth => birth.locals

private def birthEquality : (selected : Option (Birth after.declarations O Γ sort)) →
    DecidableEq (birthVariables selected)
  | none => inferInstanceAs (DecidableEq Empty)
  | some birth => birth.privateEquality

private def birthRow : (selected : Option (Birth after.declarations O Γ sort)) →
    Option (Row (birthDeclarations selected) after.declarations Γ sort)
  | none => none
  | some birth => some (birth.row.map birth.locals birth.saved birth.transport)

def outputVariables (schedule : Schedule S O Γ sort before after) (occurrence : O) : Type :=
  birthVariables (schedule.outputBirth occurrence)

def outputDeclarations (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    schedule.outputVariables occurrence → MetaArity S := birthDeclarations (schedule.outputBirth occurrence)

instance outputEquality (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    DecidableEq (schedule.outputVariables occurrence) := birthEquality (schedule.outputBirth occurrence)

def outputRow (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    Option (Row (schedule.outputDeclarations occurrence) after.declarations Γ sort) := birthRow (schedule.outputBirth occurrence)

theorem output_row_exists_iff (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    (∃ row, schedule.outputRow occurrence = some row) ↔ ∃ birth, schedule.outputBirth occurrence = some birth := by
  unfold outputRow outputDeclarations outputVariables
  cases selected : schedule.outputBirth occurrence with
  | none =>
      constructor <;> rintro ⟨_, impossible⟩ <;> cases impossible
  | some birth =>
      constructor <;> intro _
      · exact ⟨birth, rfl⟩
      · exact ⟨birth.row.map birth.locals birth.saved birth.transport, rfl⟩

theorem output_row_instances (schedule : Schedule S O Γ sort before after) (occurrence : O)
    (candidate : Assignment after.declarations next) (pattern : Term (signature S next) Γ sort) :
    (∃ row, schedule.outputRow occurrence = some row ∧
      Matches (schedule.outputDeclarations occurrence) after.declarations candidate pattern row) ↔
      ∃ birth, schedule.outputBirth occurrence = some birth ∧ birth.origin.Instances candidate pattern := by
  unfold outputRow outputDeclarations outputVariables
  cases selected : schedule.outputBirth occurrence with
  | none =>
      constructor <;> rintro ⟨_, impossible, _⟩ <;> cases impossible
  | some birth =>
      constructor
      · rintro ⟨row, same, matched⟩
        have equal := Option.some.inj same
        subst row
        exact ⟨birth, rfl, (matches_map_iff birth.locals birth.saved birth.transport candidate pattern birth.row).mp matched⟩
      · rintro ⟨original, same, matched⟩
        have equal := Option.some.inj same
        subst original
        exact ⟨birth.row.map birth.locals birth.saved birth.transport, rfl,
          (matches_map_iff birth.locals birth.saved birth.transport candidate pattern birth.row).mpr matched⟩

/-- The mixed schedule as a compiled native body. Its publication blocks are
unconstrained output-private blocks: each row keeps its own conditions. -/
abbrev native (schedule : Schedule S O Γ sort before after) : ContextualNativeBodies.Body S O Γ sort before after where
  names := schedule.names
  names_injective := schedule.names_injective
  names_preserve := schedule.names_preserve
  deltas := schedule.deltas
  final_equations := schedule.final_equations
  selections := schedule.selections
  physical_trace := schedule.physical_trace
  ShapesHold := schedule.ShapesHold
  cuts := schedule.cuts
  Admitted := schedule.Admitted
  admitted_iff := schedule.admitted_characterization
  cuts_solvable := schedule.cuts_solvable_of_final
  Extra := O
  extraIndexEquality := inferInstance
  extraVariables := schedule.outputVariables
  extraDeclarations := schedule.outputDeclarations
  extraEquality := schedule.outputEquality
  extraConditions _ := []
  extraIndices := []
  extras_solvable _ occurrence := ⟨schedule.outputVariables occurrence, schedule.outputDeclarations occurrence,
    generator _, (by intro equation member; cases member)⟩
  initialInputs := schedule.initialInputs
  net_input_is_initial := schedule.net_input_is_initial
  initial_inputs_realize_together := fun shapes {_} {_} candidate model inputs used =>
    schedule.initial_inputs_realize_together shapes candidate model inputs used
  entryCuts := schedule.entryCuts
  entry_cuts_length := schedule.entry_cuts_length
  entry_cuts_compare := schedule.entry_cuts_compare
  entry_cut_inputs := schedule.entry_cut_inputs
  entry_cut_world := schedule.entry_cut_world
  entry_cut_created_not_initial := schedule.entry_cut_created_not_initial

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
