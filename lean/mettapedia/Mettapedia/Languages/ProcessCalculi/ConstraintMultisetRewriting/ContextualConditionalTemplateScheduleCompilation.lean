import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules

/-!
# Admission compilation for mixed conditional-template bodies

The compiler collects independent source equations, original guard cuts,
physical resource history and conditional birth descriptions. Its resource
condition retains intermediate freshness. Admission is characterized in
both directions without a source execution supplied to the compiled side.
Native one-firing realization of this mixed grammar is a further comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualGuardMatching
open ContextualSourceSchedules hiding Schedule Birth Plan
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O V : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
    {declaration : V → MetaArity S}

namespace Schedule

variable {First Middle Last : Type} {first : First → MetaArity S}
    {middle : Middle → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {mid : ContextualClauseSourceState.World middle O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem frame_segment_assignment (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    (Schedule.segment past plain).frame.assignment = Assignment.compose plain.frame.assignment past.frame.assignment :=
  Extension.trans_assignment past.frame plain.frame

theorem frame_template_assignment {Query Inner : Type} [DecidableEq Middle] [DecidableEq Query] [DecidableEq Inner]
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
    (rule : ContextualConditionalTemplateSource.Rule queries inners mid.declarations Γ sort) (picked : Selection O) :
    (Schedule.template mid past queries inners rule picked).frame.assignment =
      Assignment.compose (captureFrame (ContextualTemplateSource.Expanded queries inners) middle mid.declarations).assignment
        past.frame.assignment :=
  Extension.trans_assignment past.frame (captureFrame (ContextualTemplateSource.Expanded queries inners) middle mid.declarations)

theorem final_equations (schedule : Schedule S O Γ sort before after) :
    after.equations = ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas := by
  induction schedule with
  | nil start =>
      change start.equations = ContextualResidual.mapProblem (generator start.declarations) start.equations ++ []
      simp [ContextualResidual.mapProblem, instantiateObservation_identity]
  | segment past plain prior =>
      rw [plain.final_equations, prior]
      change ContextualResidual.mapProblem plain.frame.assignment
          (ContextualResidual.mapProblem past.frame.assignment _ ++ past.deltas) ++ plain.deltas = _
      rw [ContextualResidual.mapProblem, List.map_append]
      change _ = ContextualResidual.mapProblem (Schedule.segment past plain).frame.assignment _ ++
        (ContextualResidual.mapProblem plain.frame.assignment past.deltas ++ plain.deltas)
      rw [frame_segment_assignment, ← ContextualConditionalNaturality.map_problem_compose]
      exact List.append_assoc _ _ _
  | template mid past queries inners rule picked prior =>
      change ContextualClauseSourceState.information (ContextualTemplateSource.Expanded queries inners) _ mid
        (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked = _
      rw [information_eq, prior]
      change ContextualResidual.mapProblem _ (ContextualResidual.mapProblem past.frame.assignment _ ++ past.deltas) ++ _ = _
      rw [ContextualResidual.mapProblem, List.map_append]
      change _ = ContextualResidual.mapProblem (Schedule.template mid past queries inners rule picked).frame.assignment _ ++ (_ ++ _)
      rw [frame_template_assignment, ← ContextualConditionalNaturality.map_problem_compose]
      exact List.append_assoc _ _ _

theorem source_solvable (schedule : Schedule S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations) :
    ContextualConditionalExecution.Solvable before.equations := by
  obtain ⟨Future, future, candidate, model⟩ := consistent
  rw [schedule.final_equations] at model
  have incoming := (ContextualResidual.models_mapProblem _ _ _).mp
    ((ContextualResidual.models_append candidate _ _).mp model).1
  exact ⟨Future, future, Assignment.compose candidate schedule.frame.assignment, incoming⟩

theorem commits_segment (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    (Schedule.segment past plain).commits = past.commits ++ plain.commits := List.map_append

theorem commits_template {Query Inner : Type} [DecidableEq Middle] [DecidableEq Query] [DecidableEq Inner]
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
    (rule : ContextualConditionalTemplateSource.Rule queries inners mid.declarations Γ sort) (picked : Selection O) :
    (Schedule.template mid past queries inners rule picked).commits = past.commits ++ [picked.commit] := List.map_append

theorem physical_trace (schedule : Schedule S O Γ sort before after) :
    fireList before.present schedule.commits = after.present := by
  induction schedule with
  | nil _ => rfl
  | segment past plain prior =>
      rw [commits_segment, fireList_append, prior, plain.physical_trace]
  | template mid past queries inners rule picked prior =>
      rw [commits_template, fireList_append, prior]
      rfl

def ShapesHold (schedule : Schedule S O Γ sort before after) := ∀ shape ∈ schedule.shapes, shape.Holds
def CutsHold (schedule : Schedule S O Γ sort before after) := ∀ cut ∈ schedule.cuts, cut.Holds

theorem shapes_segment (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    (Schedule.segment past plain).ShapesHold ↔ past.ShapesHold ∧ plain.ShapesHold :=
  List.forall_mem_append

theorem shapes_template {Query Inner : Type} [DecidableEq Middle] [DecidableEq Query] [DecidableEq Inner]
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
    (rule : ContextualConditionalTemplateSource.Rule queries inners mid.declarations Γ sort) (picked : Selection O) :
    (Schedule.template mid past queries inners rule picked).ShapesHold ↔ past.ShapesHold ∧
      (originalShape mid (ContextualTemplateSource.Expanded queries inners)
        (ContextualConditionalTemplateState.rawPlan queries inners middle mid rule) picked).Holds := by
  simp only [ShapesHold, shapes, List.forall_mem_append, List.forall_mem_singleton]

omit [DecidableEq O] in
private theorem mapped_cuts_iff
    (cuts : List (Cut declaration O Γ sort)) (extension : Extension declaration) :
    (∀ cut ∈ cuts.map (Cut.map extension.assignment), cut.Holds) ↔ ∀ cut ∈ cuts, cut.Holds := by
  simp only [List.forall_mem_map, Cut.extension_iff]

theorem cuts_segment (past : Schedule S O Γ sort before mid)
    (plain : ContextualSourceSchedules.Schedule S O Γ sort mid after) :
    (Schedule.segment past plain).CutsHold ↔ past.CutsHold ∧ plain.CutsHold := by
  change (∀ cut ∈ past.cuts.map (Cut.map plain.frame.assignment) ++ plain.cuts, cut.Holds) ↔ _
  rw [List.forall_mem_append, mapped_cuts_iff]
  rfl

theorem cuts_template {Query Inner : Type} [DecidableEq Middle] [DecidableEq Query] [DecidableEq Inner]
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S) (inners : Inner → MetaArity S)
    (rule : ContextualConditionalTemplateSource.Rule queries inners mid.declarations Γ sort) (picked : Selection O) :
    (Schedule.template mid past queries inners rule picked).CutsHold ↔ past.CutsHold ∧
      (originalCut mid (ContextualTemplateSource.Expanded queries inners)
        (ContextualConditionalTemplateState.rawPlan queries inners middle mid rule) picked).Holds := by
  change (∀ cut ∈ past.cuts.map (Cut.map (captureFrame (ContextualTemplateSource.Expanded queries inners) middle mid.declarations).assignment) ++
    [originalCut mid (ContextualTemplateSource.Expanded queries inners)
      (ContextualConditionalTemplateState.rawPlan queries inners middle mid rule) picked], cut.Holds) ↔ _
  rw [List.forall_mem_append, mapped_cuts_iff]
  simp only [List.forall_mem_singleton]
  rfl

theorem admitted_characterization (schedule : Schedule S O Γ sort before after) :
    schedule.Admitted ↔ schedule.ShapesHold ∧
      Executable ContextualSourceSchedules.Schedule.unitLabel before.present schedule.commits ∧
      ContextualConditionalExecution.Solvable after.equations ∧ schedule.CutsHold := by
  induction schedule with
  | nil start =>
      constructor
      · intro consistent
        exact ⟨by simp [ShapesHold, shapes], .nil _, consistent, by simp [CutsHold, cuts]⟩
      · rintro ⟨_, _, consistent, _⟩
        exact consistent
  | segment past plain prior =>
      change past.Admitted ∧ plain.Admitted ↔ _
      rw [shapes_segment, cuts_segment, commits_segment, executable_append_iff, past.physical_trace]
      constructor
      · rintro ⟨earlier, current⟩
        obtain ⟨shapes, resources, _, cuts⟩ := prior.mp earlier
        obtain ⟨shape, enabled, consistent, cut⟩ := plain.admitted_characterization.mp current
        exact ⟨⟨shapes, shape⟩, ⟨resources, enabled⟩, consistent, ⟨cuts, cut⟩⟩
      · rintro ⟨⟨shapes, shape⟩, ⟨resources, enabled⟩, consistent, ⟨cuts, cut⟩⟩
        exact ⟨prior.mpr ⟨shapes, resources, plain.source_solvable consistent, cuts⟩,
          plain.admitted_characterization.mpr ⟨shape, enabled, consistent, cut⟩⟩
  | template mid past queries inners rule picked prior =>
      change past.Admitted ∧ ContextualConditionalTemplateState.Admitted queries inners _ mid rule picked ↔ _
      rw [shapes_template, cuts_template, commits_template, executable_snoc_iff, past.physical_trace]
      constructor
      · rintro ⟨earlier, current⟩
        obtain ⟨shapes, resources, _, cuts⟩ := prior.mp earlier
        obtain ⟨shape, enabled, consistent, cut⟩ :=
          (clause_admitted_iff mid (ContextualTemplateSource.Expanded queries inners)
            (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked).mp current
        exact ⟨⟨shapes, shape⟩, ⟨resources, enabled⟩, consistent, ⟨cuts, cut⟩⟩
      · rintro ⟨⟨shapes, shape⟩, ⟨resources, enabled⟩, consistent, ⟨cuts, cut⟩⟩
        have earlierConsistent := (Schedule.template mid (Schedule.nil mid) queries inners rule picked).source_solvable consistent
        exact ⟨prior.mpr ⟨shapes, resources, earlierConsistent, cuts⟩,
          (clause_admitted_iff mid (ContextualTemplateSource.Expanded queries inners)
            (ContextualConditionalTemplateState.rawPlan queries inners _ mid rule) picked).mpr ⟨shape, enabled, consistent, cut⟩⟩

end Schedule

structure Plan (declaration : V → MetaArity S) (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  shapes : List (Shape O)
  resources : CompiledSchedule O Unit
  problem : ContextualResidual.Problem declaration
  cuts : List (Cut declaration O context sort)
  births : List (Birth declaration O context sort)

def Plan.Holds (plan : Plan declaration O Γ sort) (world : Finset O) : Prop :=
  (∀ shape ∈ plan.shapes, shape.Holds) ∧ plan.resources.condition.Holds ContextualSourceSchedules.Schedule.unitLabel world ∧
    ContextualConditionalExecution.Solvable plan.problem ∧ (∀ cut ∈ plan.cuts, cut.Holds)

namespace Schedule

variable {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def compile (schedule : Schedule S O Γ sort before after) : Plan after.declarations O Γ sort where
  shapes := schedule.shapes
  resources := CompiledSchedule.compile ContextualSourceSchedules.Schedule.unitLabel schedule.commits
  problem := ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas
  cuts := schedule.cuts
  births := schedule.births

theorem compile_exact (schedule : Schedule S O Γ sort before after) :
    schedule.compile.Holds before.present ↔ schedule.Admitted := by
  unfold Plan.Holds compile
  rw [CompiledSchedule.compile_condition_iff, ← schedule.final_equations]
  exact schedule.admitted_characterization.symm

theorem compile_effect (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) :
    Enabled ContextualSourceSchedules.Schedule.unitLabel before.present schedule.compile.resources.effect ∧
      fire before.present schedule.compile.resources.effect = after.present := by
  obtain ⟨enabled, same⟩ := (CompiledSchedule.compile_correct ContextualSourceSchedules.Schedule.unitLabel
    schedule.commits before.present).2 accepted.2.1
  exact ⟨enabled, same.trans schedule.physical_trace⟩

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSchedules
