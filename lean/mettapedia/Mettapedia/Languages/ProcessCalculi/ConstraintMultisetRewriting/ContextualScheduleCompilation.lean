import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleMetadata

/-!
# Compiling selected private clauses to explicit admission data

Compilation collects shapes, binding equations, original guard cuts and
production origins, and computes a net occurrence update with an initial
precondition. Its admission test does not execute the source schedule.

The resource projection forgets values only for occurrence bookkeeping;
contextual information, guards and production values remain in separate
fields. Atomic publication of the collected production origins is a further
obligation, not part of the occurrence-set result below.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualGuardMatching ContextualConditionalRows
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O Local Query V : Type} [DecidableEq O]
    {locals : Local → MetaArity S} {declaration : V → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

theorem clause_admitted_iff (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) :
    ContextualClauseSourceState.Admitted queries locals before plan picked ↔
      (originalShape before queries plan picked).Holds ∧
      Enabled Schedule.unitLabel before.present (picked.commit : Commit O Unit) ∧
      ContextualConditionalExecution.Solvable (ContextualClauseSourceState.information queries locals before plan picked) ∧
      (originalCut before queries plan picked).Holds := by
  constructor
  · intro admitted
    refine ⟨⟨admitted.take_distinct, admitted.output_distinct, admitted.take_shape,
      admitted.read_shape, admitted.output_shape⟩,
      ⟨admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh, ?_⟩,
      admitted.solvable, ?_⟩
    · simp [Selection.commit]
    · simpa only [Cut.Holds, originalCut, List.forall_mem_map,
        ContextualClauseSourceState.information] using admitted.checks
  · rintro ⟨shape, resources, consistent, guarded⟩
    refine ⟨shape.1, shape.2.1, shape.2.2.1, shape.2.2.2.1, shape.2.2.2.2,
      resources.taken_subset, resources.kept_subset, resources.apart, resources.fresh,
      consistent, ?_⟩
    simpa only [Cut.Holds, originalCut, List.forall_mem_map,
      ContextualClauseSourceState.information] using guarded

namespace Schedule

variable {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

theorem commits_snoc {Middle Query : Type} {middle : Middle → MetaArity S}
    [DecidableEq Middle] [DecidableEq Query] {mid : ContextualClauseSourceState.World middle O Γ sort}
    (past : Schedule S O Γ sort before mid) (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries mid.declarations)) Γ sort))
    (picked : Selection O) :
    (Schedule.snoc past queries plan picked).commits = past.commits ++ [picked.commit] := by
  exact List.map_append

/-- Every source admission obligation is retained in the compiled data. -/
theorem admitted_characterization (schedule : Schedule S O Γ sort before after) :
    schedule.Admitted ↔ schedule.ShapesHold ∧ Executable unitLabel before.present schedule.commits ∧
      ContextualConditionalExecution.Solvable after.equations ∧ schedule.CutsHold := by
  induction schedule with
  | nil start =>
      constructor
      · intro consistent
        exact ⟨by simp [ShapesHold, shapes], .nil _, consistent, by simp [CutsHold, cuts]⟩
      · rintro ⟨_, _, consistent, _⟩
        exact consistent
  | @snoc Middle Query _ middle _ _ start mid past queries plan picked prior =>
      change past.Admitted ∧ ContextualClauseSourceState.Admitted queries middle mid plan picked ↔ _
      rw [shapes_snoc, cuts_snoc, commits_snoc, executable_snoc_iff, past.physical_trace]
      constructor
      · rintro ⟨earlier, current⟩
        obtain ⟨shapes, resources, _consistent, cuts⟩ := prior.mp earlier
        obtain ⟨shape, enabled, consistent, cut⟩ := (clause_admitted_iff mid queries plan picked).mp current
        exact ⟨⟨shapes, shape⟩, ⟨resources, enabled⟩, consistent, ⟨cuts, cut⟩⟩
      · rintro ⟨⟨shapes, shape⟩, ⟨resources, enabled⟩, consistent, ⟨cuts, cut⟩⟩
        have earlierConsistent := (Schedule.snoc (Schedule.nil mid) queries plan picked).source_solvable consistent
        exact ⟨prior.mpr ⟨shapes, resources, earlierConsistent, cuts⟩,
          (clause_admitted_iff mid queries plan picked).mpr ⟨shape, enabled, consistent, cut⟩⟩

end Schedule

structure Plan (declaration : V → MetaArity S) (O : Type) (context : Ctx S) (sort : S.Srt) : Type 1 where
  shapes : List (Shape O)
  resources : CompiledSchedule O Unit
  problem : ContextualResidual.Problem declaration
  cuts : List (Cut declaration O context sort)
  births : List (Birth declaration O context sort)

def Plan.Holds (plan : Plan declaration O Γ sort) (world : Finset O) : Prop :=
  (∀ shape ∈ plan.shapes, shape.Holds) ∧ plan.resources.condition.Holds Schedule.unitLabel world ∧
    ContextualConditionalExecution.Solvable plan.problem ∧ (∀ cut ∈ plan.cuts, cut.Holds)

namespace Schedule

variable {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

def compile (schedule : Schedule S O Γ sort before after) : Plan after.declarations O Γ sort where
  shapes := schedule.shapes
  resources := CompiledSchedule.compile unitLabel schedule.commits
  problem := ContextualResidual.mapProblem schedule.frame.assignment before.equations ++ schedule.deltas
  cuts := schedule.cuts
  births := schedule.births

/-- Compilation preserves and reflects admission, including unsuccessful schedules. -/
theorem compile_exact (schedule : Schedule S O Γ sort before after) :
    schedule.compile.Holds before.present ↔ schedule.Admitted := by
  unfold Plan.Holds compile
  rw [CompiledSchedule.compile_condition_iff, ← schedule.final_equations]
  exact schedule.admitted_characterization.symm

/-- The computed resource update is enabled and gives exactly the source's final occurrence set. -/
theorem compile_effect (schedule : Schedule S O Γ sort before after)
    (accepted : schedule.compile.Holds before.present) :
    Enabled unitLabel before.present schedule.compile.resources.effect ∧
      fire before.present schedule.compile.resources.effect = after.present := by
  obtain ⟨enabled, same⟩ := (CompiledSchedule.compile_correct unitLabel schedule.commits before.present).2 accepted.2.1
  exact ⟨enabled, same.trans schedule.physical_trace⟩

end Schedule

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceSchedules
