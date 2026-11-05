import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUniformBirthProblem
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation

/-!
# One information problem retains every original guard countermodel

Each original guard cut receives a private declaration block beside the
current caller and the output creation blocks. Consistency follows from
terminal information alone, without assuming that the guards passed.
Admission is preserved and reflected by the joint problem and the guards
on their original worlds. This is an information/observation compilation;
representing those worlds in a native entry inventory is a separate step.
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

abbrev CutIndex (schedule : Schedule S O Γ sort before after) := Fin schedule.cuts.length
abbrev GuardBlockIndex (schedule : Schedule S O Γ sort before after) := Sum schedule.BlockIndex schedule.CutIndex

def guardVariables (schedule : Schedule S O Γ sort before after) : schedule.GuardBlockIndex → Type
  | .inl index => schedule.blockVariables index
  | .inr _ => after.Names

def guardDeclarations (schedule : Schedule S O Γ sort before after) :
    ∀ index, schedule.guardVariables index → MetaArity S
  | .inl index => schedule.blockDeclarations index
  | .inr _ => after.declarations

def guardConditions (schedule : Schedule S O Γ sort before after) :
    ∀ index, ContextualResidual.Problem (schedule.guardDeclarations index)
  | .inl index => schedule.blockConditions index
  | .inr index => (schedule.cuts.get index).problem

def guardIndices (schedule : Schedule S O Γ sort before after) : List schedule.GuardBlockIndex :=
  schedule.blockIndices.map Sum.inl ++ (List.finRange schedule.cuts.length).map Sum.inr

theorem guard_index_list_complete (schedule : Schedule S O Γ sort before after) (index : schedule.GuardBlockIndex) :
    index ∈ schedule.guardIndices := by
  cases index with
  | inl index => exact List.mem_append_left _ (List.mem_map.mpr ⟨index, schedule.block_list_complete index, rfl⟩)
  | inr index => exact List.mem_append_right _ (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)

abbrev guardFamily (schedule : Schedule S O Γ sort before after) :=
  ContextualIndependentProblems.family schedule.guardVariables schedule.guardDeclarations

instance guardEquality (schedule : Schedule S O Γ sort before after) :
    DecidableEq (ContextualAnswerFamilies.Names schedule.guardVariables) := by
  letI : ∀ index, DecidableEq (schedule.guardVariables index) := fun index =>
    match index with
    | .inl none => after.equality
    | .inl (some index) => (schedule.births.get index).equality
    | .inr _ => after.equality
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
      | some index => exact schedule.births_solvable_of_final consistent _ (List.get_mem _ _)
  | inr index => exact schedule.cuts_solvable_of_final consistent _ (List.get_mem _ _)

/-- The extra blocks reject no consistent terminal model, including for a body with a false earlier guard. -/
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

def guardView (schedule : Schedule S O Γ sort before after) (index : schedule.CutIndex) :
    Cut schedule.guardFamily O Γ sort :=
  let cut := schedule.cuts.get index
  let embedding := ContextualIndependentProblems.inclusion schedule.guardVariables schedule.guardDeclarations (.inr index)
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
    (schedule.guard_blocks_solvable consistent) schedule.guardIndices (.inr index) (schedule.guard_index_list_complete _)
    (schedule.cuts.get index).locals (schedule.cuts.get index).rows (schedule.cuts.get index).world check

/-- Exact source admission without presupposing any guard verdict in the compilation. -/
theorem guarded_admission_iff (schedule : Schedule S O Γ sort before after) :
    ((∀ shape ∈ schedule.shapes, shape.Holds) ∧
      schedule.compile.resources.condition.Holds unitLabel before.present ∧
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

def reducedGuardView (schedule : Schedule S O Γ sort before after)
    (update : ContextualFrameUpdate.Update schedule.guardProblem) (index : schedule.CutIndex) :
    Cut update.declaration O Γ sort :=
  { (schedule.guardView index).map update.answer with problem := update.remaining }

/-- Solver reduction keeps all original countermodels, even with a nonempty remaining queue. -/
theorem reduced_guard_view_iff (schedule : Schedule S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations)
    (update : ContextualFrameUpdate.Update schedule.guardProblem) (index : schedule.CutIndex) :
    (schedule.reducedGuardView update index).Holds ↔ (schedule.cuts.get index).Holds := by
  apply Iff.trans ?_ (schedule.guard_view_iff consistent index)
  simp only [Cut.Holds, reducedGuardView, Cut.map, List.forall_mem_map]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  constructor
  · intro asked Future future candidate model
    obtain ⟨residual, residualModel, images⟩ := update.factors future candidate model
    have held := (ContextualConditionalGuards.holds_transport (schedule.guardView index).locals update.answer residual
      (schedule.guardView index).rows (schedule.guardView index).world check).mp
      (asked Future future residual residualModel)
    have same : candidate = Assignment.compose residual update.answer := funext images
    exact same.symm ▸ held
  · intro asked Future future candidate model
    apply (ContextualConditionalGuards.holds_transport (schedule.guardView index).locals update.answer candidate
      (schedule.guardView index).rows (schedule.guardView index).world check).mpr
    exact asked Future future _ (update.valid.sound future candidate model)

/-- An actual bounded worklist return retains the original guard verdicts; it need not finish. -/
theorem actual_guard_update [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (schedule : Schedule S O Γ sort before after) (consistent : ContextualConditionalExecution.Solvable after.equations)
    (fuel : Nat) :
    ∃ update : ContextualFrameUpdate.Update schedule.guardProblem,
      ContextualFrameWorklist.run fuel schedule.guardFamily schedule.guardProblem = .residual update ∧
        ∀ index : schedule.CutIndex,
          (schedule.reducedGuardView update index).Holds ↔ (schedule.cuts.get index).Holds := by
  cases computed : ContextualFrameWorklist.run fuel schedule.guardFamily schedule.guardProblem with
  | refuted impossible =>
      obtain ⟨Future, future, candidate, model⟩ := schedule.guard_problem_solvable_iff.mpr consistent
      exact False.elim (impossible future candidate model)
  | residual update =>
      exact ⟨update, rfl, fun index => schedule.reduced_guard_view_iff consistent update index⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules.Schedule
