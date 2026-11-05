import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateAllocation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedScheduleProblem

/-!
# Mixed bodies retain original guard countermodels in one problem

The current information and each saved guard cut have independent tagged
declarations. Output conditions remain in their saved rows rather than
becoming global obligations. The construction is computed from source
syntax, entry information and cuts, before admission or native execution.
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

abbrev CutIndex (schedule : Schedule S O Γ sort before after) := Fin schedule.cuts.length
abbrev GuardBlockIndex (schedule : Schedule S O Γ sort before after) := Sum (Option schedule.CutIndex) O

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

def currentProblem (schedule : Schedule S O Γ sort before after) : ContextualResidual.Problem after.declarations :=
  ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas

def guardVariables (schedule : Schedule S O Γ sort before after) : schedule.GuardBlockIndex → Type
  | .inl _ => after.Names
  | .inr occurrence => schedule.outputVariables occurrence
def guardDeclarations (schedule : Schedule S O Γ sort before after) : ∀ index, schedule.guardVariables index → MetaArity S :=
  fun index => match index with
    | .inl _ => after.declarations
    | .inr occurrence => schedule.outputDeclarations occurrence

def guardConditions (schedule : Schedule S O Γ sort before after) :
    ∀ index, ContextualResidual.Problem (schedule.guardDeclarations index)
  | .inl none => schedule.currentProblem
  | .inl (some index) => (schedule.cuts.get index).problem
  | .inr _ => []

def guardIndices (schedule : Schedule S O Γ sort before after) : List schedule.GuardBlockIndex :=
  (none :: (List.finRange schedule.cuts.length).map some).map Sum.inl

theorem guard_index_list_complete (schedule : Schedule S O Γ sort before after) (index : Option schedule.CutIndex) :
    Sum.inl index ∈ schedule.guardIndices := by
  apply List.mem_map.mpr
  refine ⟨index, ?_, rfl⟩
  cases index with
  | none => exact List.mem_cons_self
  | some index => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)

abbrev guardFamily (schedule : Schedule S O Γ sort before after) :=
  ContextualIndependentProblems.family schedule.guardVariables schedule.guardDeclarations

instance guardEquality (schedule : Schedule S O Γ sort before after) :
    DecidableEq (ContextualAnswerFamilies.Names schedule.guardVariables) := by
  let _ : ∀ index, DecidableEq (schedule.guardVariables index) := fun index =>
    match index with
    | .inl _ => after.equality
    | .inr occurrence => schedule.outputEquality occurrence
  infer_instance

def guardProblem (schedule : Schedule S O Γ sort before after) : ContextualResidual.Problem schedule.guardFamily :=
  ContextualIndependentProblems.problem schedule.guardVariables schedule.guardDeclarations schedule.guardConditions schedule.guardIndices

theorem guard_blocks_solvable (schedule : Schedule S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (index : schedule.GuardBlockIndex) :
    ContextualConditionalExecution.Solvable (schedule.guardConditions index) := by
  cases index with
  | inl index =>
      cases index with
      | none =>
          change ContextualConditionalExecution.Solvable schedule.currentProblem
          rw [currentProblem, ← schedule.final_equations]
          exact consistent
      | some index => exact schedule.cuts_solvable_of_final consistent _ (List.get_mem _ _)
  | inr occurrence =>
      exact ⟨schedule.outputVariables occurrence, schedule.outputDeclarations occurrence,
        generator _, (by intro equation member; cases member)⟩

theorem guard_problem_solvable_iff (schedule : Schedule S O Γ sort before after) :
    ContextualConditionalExecution.Solvable schedule.guardProblem ↔
      ContextualConditionalExecution.Solvable after.equations := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    have current := (ContextualIndependentProblems.models_iff schedule.guardVariables schedule.guardDeclarations
      schedule.guardConditions schedule.guardIndices candidate).mp model (.inl none) (schedule.guard_index_list_complete _)
    change ContextualResidual.Models _ schedule.currentProblem at current
    rw [currentProblem, ← schedule.final_equations] at current
    exact ⟨Future, future, _, current⟩
  · intro consistent
    exact ContextualIndependentProblems.solvable schedule.guardVariables schedule.guardDeclarations schedule.guardConditions
      (schedule.guard_blocks_solvable consistent) schedule.guardIndices

def guardView (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) : Cut schedule.guardFamily O Γ sort :=
  let cut := schedule.cuts.get index
  let embedding := ContextualIndependentProblems.inclusion schedule.guardVariables schedule.guardDeclarations (.inl (some index))
  { cut.map embedding with problem := schedule.guardProblem }

theorem guard_view_iff (schedule : Schedule S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (index : schedule.CutIndex) :
    (schedule.guardView index).Holds ↔ (schedule.cuts.get index).Holds := by
  simp only [Cut.Holds, guardView, Cut.map, List.forall_mem_map]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  exact ContextualIndependentProblems.asks_iff schedule.guardVariables schedule.guardDeclarations schedule.guardConditions
    (schedule.guard_blocks_solvable consistent) schedule.guardIndices (.inl (some index)) (schedule.guard_index_list_complete _)
    (schedule.cuts.get index).locals (schedule.cuts.get index).rows (schedule.cuts.get index).world check

theorem guarded_admission_iff (schedule : Schedule S O Γ sort before after) :
    (schedule.ShapesHold ∧
      schedule.compile.resources.condition.Holds ContextualSourceSchedules.Schedule.unitLabel before.present ∧
      ContextualConditionalExecution.Solvable schedule.guardProblem ∧
      ∀ index : schedule.CutIndex, (schedule.guardView index).Holds) ↔ schedule.Admitted := by
  rw [← schedule.compile_exact]
  constructor
  · rintro ⟨shapes, resources, consistent, guards⟩
    have terminal := schedule.guard_problem_solvable_iff.mp consistent
    refine ⟨shapes, resources, ?_, ?_⟩
    · change ContextualConditionalExecution.Solvable
        (ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas)
      rw [← schedule.final_equations]
      exact terminal
    · intro cut member
      obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
      exact (schedule.guard_view_iff terminal index).mp (guards index)
  · rintro ⟨shapes, resources, consistent, guards⟩
    have terminal : ContextualConditionalExecution.Solvable after.equations := by
      rw [schedule.final_equations]
      exact consistent
    refine ⟨shapes, resources, schedule.guard_problem_solvable_iff.mpr terminal, ?_⟩
    intro index
    exact (schedule.guard_view_iff terminal index).mpr (guards _ (List.get_mem _ _))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules.Schedule
