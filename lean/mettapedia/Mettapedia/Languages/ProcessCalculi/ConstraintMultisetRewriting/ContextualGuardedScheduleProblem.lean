import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleInputModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEntryGuardCompilation

/-!
# Ordinary/shared schedules as compiled native bodies

Each original guard cut and each saved birth keeps a private declaration
block beside the current caller. Consistency of every block follows from
terminal information alone, without assuming that the guards passed.
The body supplies the selections, shapes, cuts and their entry
representations, the admission characterization and net-input facts; the guard problem, its views and the
exact guarded admission are then the generic ones of `ContextualNativeBodies`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConditionalRows

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

/-- Guard truth is not needed to establish consistency of earlier creation conditions. -/
theorem births_solvable_of_final (schedule : Schedule S O Γ sort before after) :
    ContextualConditionalExecution.Solvable after.equations →
      ∀ birth ∈ schedule.births, ContextualConditionalExecution.Solvable birth.problem := by
  induction schedule with
  | nil _ => intro _consistent birth member; cases member
  | @snoc Middle Query _ middle _ _ _ mid past queries plan picked prior =>
      intro consistent birth member
      change birth ∈ past.births.map (Birth.map (captureFrame queries middle mid.declarations).assignment) ++
        originalBirths mid queries plan picked at member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp earlier
        exact prior ((Schedule.snoc (Schedule.nil mid) queries plan picked).source_solvable consistent) original oldMember
      · unfold originalBirths at current
        obtain ⟨port, rfl⟩ := List.mem_ofFn.mp current
        exact consistent

theorem cuts_solvable_of_final (schedule : Schedule S O Γ sort before after) :
    ContextualConditionalExecution.Solvable after.equations →
      ∀ cut ∈ schedule.cuts, ContextualConditionalExecution.Solvable cut.problem := by
  induction schedule with
  | nil _ => intro _consistent cut member; cases member
  | @snoc Middle Query _ middle _ _ _ mid past queries plan picked prior =>
      intro consistent cut member
      change cut ∈ past.cuts.map (Cut.map (captureFrame queries middle mid.declarations).assignment) ++
        [originalCut mid queries plan picked] at member
      rcases List.mem_append.mp member with earlier | current
      · obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp earlier
        exact (ContextualConditionalNaturality.solvable_extension_iff
          (captureFrame queries middle mid.declarations) original.problem).mpr
          (prior ((Schedule.snoc (Schedule.nil mid) queries plan picked).source_solvable consistent) original oldMember)
      · have only := List.mem_singleton.mp current
        subst cut
        exact consistent

/-- The schedule as a compiled native body. Its publication blocks are its
saved births: each keeps its creation-time problem. -/
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
  Extra := schedule.BirthIndex
  extraIndexEquality := inferInstance
  extraVariables index := (schedule.births.get index).SavedNames
  extraDeclarations index := (schedule.births.get index).saved
  extraEquality index := (schedule.births.get index).equality
  extraConditions index := (schedule.births.get index).problem
  extraIndices := List.finRange schedule.births.length
  extras_solvable consistent index := schedule.births_solvable_of_final consistent _ (List.get_mem schedule.births index)
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

theorem native_birth_listed (schedule : Schedule S O Γ sort before after) (index : schedule.BirthIndex) :
    Sum.inl (some index) ∈ schedule.native.guardIndices :=
  schedule.native.guard_index_extra_listed index (List.mem_finRange index)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
