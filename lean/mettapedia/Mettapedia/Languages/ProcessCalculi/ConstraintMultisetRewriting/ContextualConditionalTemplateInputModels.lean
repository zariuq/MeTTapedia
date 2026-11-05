import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateOriginSemantics
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleInputModels

/-!
# Mixed-body source models supply their used entry-row witnesses

The input set excludes rows already created inside the body. Each given
final information model supplies a matching witness for every used entry
row, preserving its caller assignment. Finite witnesses can then be opened
jointly in a fresh declaration extension. Unused row conditions are absent
from these obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations
open ContextualSourceSchedules hiding Schedule Birth Plan

variable {S : Signature} {O First Last Next : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {next : Next → MetaArity S}
    {Γ : Ctx S} {sort : S.Srt}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def creations (schedule : Schedule S O Γ sort before after) : Finset O :=
  (schedule.selections.flatMap (fun picked => picked.made)).toFinset

theorem not_mem_creations (schedule : Schedule S O Γ sort before after) (occurrence : O) :
    occurrence ∉ schedule.creations ↔ ∀ picked ∈ schedule.selections, occurrence ∉ picked.made := by
  simp only [creations, List.mem_toFinset, List.mem_flatMap, not_exists, not_and]

def initialInputs : {Last : Type} → {last : Last → MetaArity S} →
    {after : ContextualClauseSourceState.World last O Γ sort} →
    Schedule S O Γ sort before after → Finset O
  | _, _, _, .nil _ => ∅
  | _, _, _, .segment past plain => past.initialInputs ∪ (plain.initialInputs \ past.creations)
  | _, _, _, @Schedule.template _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ past _ _ _ picked =>
      past.initialInputs ∪ ((picked.taken.toFinset ∪ picked.read.toFinset) \ past.creations)

theorem model_at_entry (schedule : Schedule S O Γ sort before after)
    (candidate : Assignment after.declarations next) (model : ContextualResidual.Models candidate after.equations) :
    ContextualResidual.Models (Assignment.compose candidate schedule.frame.assignment) before.equations := by
  rw [schedule.final_equations] at model
  exact (ContextualResidual.models_mapProblem _ _ _).mp
    ((ContextualResidual.models_append candidate _ _).mp model).1

theorem initial_input_matches (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) (occurrence : O)
    (used : occurrence ∈ schedule.initialInputs) :
    ∃ pattern : Term (signature S next) Γ sort,
      Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment)
        pattern (before.rows occurrence) := by
  induction schedule with
  | nil start => exact False.elim (Finset.notMem_empty _ used)
  | segment past plain prior =>
      have parts := (shapes_segment past plain).mp shapes
      have previous := plain.model_at_entry candidate model
      change occurrence ∈ past.initialInputs ∪ (plain.initialInputs \ past.creations) at used
      rcases Finset.mem_union.mp used with old | current
      · obtain ⟨pattern, matched⟩ := prior parts.1
          (Assignment.compose candidate plain.frame.assignment) previous old
        refine ⟨pattern, ?_⟩
        rw [frame_segment_assignment, Assignment.compose_associative]
        exact matched
      · have current := Finset.mem_sdiff.mp current
        obtain ⟨pattern, matched⟩ := plain.initial_input_matches parts.2 candidate model occurrence current.1
        have missing := (past.outputBirth_none_iff_shapes parts.1 occurrence).mpr
          ((past.not_mem_creations occurrence).mp current.2)
        have original := (past.retained_entry_instances parts.1 occurrence missing next
          (Assignment.compose candidate plain.frame.assignment) pattern).mpr matched
        refine ⟨pattern, ?_⟩
        rw [frame_segment_assignment, Assignment.compose_associative]
        exact original
  | template mid past queries inners rule picked prior =>
      have parts := (shapes_template past queries inners rule picked).mp shapes
      have joined : ContextualResidual.Models candidate
          (ContextualClauseSourceState.information (ContextualTemplateSource.Expanded queries inners) _ mid
            (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked) := model
      rw [information_eq] at joined
      have previous := (ContextualResidual.models_mapProblem _ _ _).mp
        ((ContextualResidual.models_append candidate _ _).mp joined).1
      change occurrence ∈ past.initialInputs ∪ ((picked.taken.toFinset ∪ picked.read.toFinset) \ past.creations) at used
      rcases Finset.mem_union.mp used with old | current
      · obtain ⟨pattern, matched⟩ := prior parts.1
          (Assignment.compose candidate (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment)
          previous old
        refine ⟨pattern, ?_⟩
        rw [frame_template_assignment, Assignment.compose_associative]
        exact matched
      · have current := Finset.mem_sdiff.mp current
        let witness := ContextualClauseWitnesses.witness_of_model (ContextualTemplateSource.Expanded queries inners) _ mid.declarations
          picked (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule).rule mid.rows mid.equations
          parts.2.2.2.1 parts.2.2.2.2.1 candidate model
        have currentMatch : ∃ pattern : Term (signature S next) Γ sort,
            Matches _ mid.declarations
              (Assignment.compose candidate (captureEmbedding (ContextualTemplateSource.Expanded queries inners) _ mid.declarations))
              pattern (mid.rows occurrence) := by
          rcases Finset.mem_union.mp current.1 with taken | read
          · obtain ⟨port, equal⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp taken)
            have realized := witness.taken port
            rw [equal] at realized
            rw [ContextualClauseWitnesses.captures_square]
            exact ⟨_, realized.matches _ mid.declarations⟩
          · obtain ⟨port, equal⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp read)
            have realized := witness.read port
            rw [equal] at realized
            rw [ContextualClauseWitnesses.captures_square]
            exact ⟨_, realized.matches _ mid.declarations⟩
        obtain ⟨pattern, matched⟩ := currentMatch
        have missing := (past.outputBirth_none_iff_shapes parts.1 occurrence).mpr
          ((past.not_mem_creations occurrence).mp current.2)
        have square := congrArg (Assignment.compose candidate)
          (captureFrame_assignment (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).symm
        have original := (past.retained_entry_instances parts.1 occurrence missing next
          (Assignment.compose candidate (captureFrame (ContextualTemplateSource.Expanded queries inners) _ mid.declarations).assignment)
          pattern).mpr (square ▸ matched)
        refine ⟨pattern, ?_⟩
        rw [frame_template_assignment, Assignment.compose_associative]
        exact original

theorem initial_inputs_realize_together (schedule : Schedule S O Γ sort before after)
    (shapes : schedule.ShapesHold) (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) (inputs : List O)
    (used : ∀ occurrence ∈ inputs, occurrence ∈ schedule.initialInputs) :
    ∃ extension : ContextualGuardMatching.Extension next, ∃ _filler : Assignment first extension.declarations,
      ∀ occurrence ∈ inputs, ∃ pattern : Term (signature S extension.declarations) Γ sort,
        Realizes first before.declarations
          (Assignment.compose extension.assignment (Assignment.compose candidate schedule.frame.assignment))
          pattern (before.rows occurrence) := by
  classical
  have witnesses : ∀ occurrence : { occurrence : O // occurrence ∈ inputs },
      ∃ pattern : Term (signature S next) Γ sort,
        Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment)
          pattern (before.rows occurrence.val) := by
    intro occurrence
    exact schedule.initial_input_matches shapes candidate model occurrence.val (used occurrence.val occurrence.property)
  let patterns := fun occurrence => Classical.choose (witnesses occurrence)
  let requests := inputs.attach.map fun occurrence => (patterns occurrence, before.rows occurrence.val)
  have matched : ∀ request ∈ requests,
      Matches first before.declarations (Assignment.compose candidate schedule.frame.assignment) request.1 request.2 := by
    intro request member
    obtain ⟨occurrence, _member, rfl⟩ := List.mem_map.mp member
    exact Classical.choose_spec (witnesses occurrence)
  obtain ⟨extension, filler, realized⟩ := finite_realizations first before.declarations
    (Assignment.compose candidate schedule.frame.assignment) requests matched
  refine ⟨extension, filler, ?_⟩
  intro occurrence member
  let index : { occurrence : O // occurrence ∈ inputs } := ⟨occurrence, member⟩
  exact ⟨instantiate extension.assignment (patterns index), realized _
    (List.mem_map.mpr ⟨index, List.mem_attach _ _, rfl⟩)⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
