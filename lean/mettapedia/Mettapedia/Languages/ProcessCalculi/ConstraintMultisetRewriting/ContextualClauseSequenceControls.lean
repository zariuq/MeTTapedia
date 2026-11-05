import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequenceComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualWorldCompilerControls

/-!
# A finite authored program computes, reuses and returns an answer

Both source clauses are declared over their exposed environments. The
first computes a key through a stored function; the second reads its
published schema twice and returns the retained answer. The source and
actual native histories preserve the exact physical selection trace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequenceControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualWorldComparison ContextualClauseSequences
open ContextualClausePublication.BinderControls (DataOperator dataSignature base locals captures queries actor origin symbol located)
open ContextualComputedJoinControls (world plan picked source_admitted)
open ContextualClauseSequencingControls (afterFirst rowLocals nextPlan selection source_next_admitted joinedWitness)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (result : base.Srt) : DecidableEq (base.Op result) := by
  change DecidableEq (DataOperator ⊕ Operator (SchematicReach.spaceDeclaration dataSignature () (Name := Nat)) result)
  infer_instance
local instance : DecidableEq world.Names := world.equality

abbrev afterFirstEnv := resultEnv queries locals captures (generator captures)
abbrev secondPublic := queryFamily captures actor
def retained : SchematicReach.Closed secondPublic := generator secondPublic (.inr (.inl true))
def secondCode : RuleInstance (SchematicReach.Closed secondPublic) :=
  ⟨[], [located 9 retained, located 9 retained], [], [.equal retained (symbol 7)], [located 10 retained]⟩
def secondPlan : ContextualPublication.Plan (SchematicReach.Closed secondPublic) := ⟨secondCode, [true], rfl⟩
def returned : SchematicReach.Closed secondPublic := located 10 retained

def program : Sequence base [] () captures :=
  .clause queries inferInstance plan (.clause captures inferInstance secondPlan (.finish returned))

theorem prepared_first_plan : preparedPlan queries (generator captures) plan = plan := by
  with_unfolding_all rfl
theorem prepared_second_plan : preparedPlan captures afterFirstEnv secondPlan = nextPlan := by
  with_unfolding_all rfl

theorem final_value :
    instantiate (resultEnv captures rowLocals origin afterFirstEnv) returned =
      queryView captures rowLocals origin
        (located 10 ContextualClauseSequencingControls.retainedAnswer) := by
  with_unfolding_all rfl

theorem source_program : SourceRun base Nat [] () captures (located 10 (symbol 7))
    world (generator captures) program [picked, selection] := by
  refine SourceRun.clause world (generator captures) queries plan _ picked [selection] ?_ ?_
  · erw [prepared_first_plan]
    exact source_admitted
  · erw [prepared_first_plan]
    refine SourceRun.clause afterFirst afterFirstEnv captures secondPlan (.finish returned) selection [] ?_ ?_
    · erw [prepared_second_plan]
      exact source_next_admitted
    · erw [prepared_second_plan]
      apply SourceRun.finish
      obtain ⟨candidate, model, _, _⟩ := joinedWitness.gives_model captures rowLocals origin
      refine ⟨ContextualGuardMatching.Extension.identity captures, candidate, model, ?_⟩
      erw [final_value]
      exact ContextualClauseSequencingControls.source_next_preserves_the_returned_answer captures candidate model

theorem actual_native_program : NativeRun base Nat [] () captures (located 10 (symbol 7))
    (world.native ∅) (generator captures) program [picked, selection] := by
  exact source_program.to_native 1 (world.native ∅) (generator captures)
    (Equivalent.refl world (generator captures))

def conflictingCode : RuleInstance (SchematicReach.Closed secondPublic) :=
  ⟨[], [located 9 retained, located 9 (symbol 9)], [], [], [located 10 retained]⟩
def conflictingPlan : ContextualPublication.Plan (SchematicReach.Closed secondPublic) := ⟨conflictingCode, [true], rfl⟩
def conflictingProgram : Sequence base [] () captures :=
  .clause queries inferInstance plan (.clause captures inferInstance conflictingPlan (.finish returned))

theorem prepared_conflicting_plan : preparedPlan captures afterFirstEnv conflictingPlan =
    ContextualClauseSequencingControls.conflictingPlan := by
  with_unfolding_all rfl

theorem no_source_program_with_the_conflicting_second_read :
    ¬ SourceRun base Nat [] () captures (located 10 (symbol 7))
      world (generator captures) conflictingProgram [picked, selection] := by
  intro run
  cases run with
  | clause _ _ _ _ _ _ _ _ tail =>
      erw [prepared_first_plan] at tail
      cases tail with
      | clause _ _ _ _ _ _ _ admitted _ =>
          erw [prepared_conflicting_plan] at admitted
          exact ContextualClauseSequencingControls.a_conflicting_second_read_cannot_fire admitted

theorem no_native_program_with_the_conflicting_second_read :
    ¬ NativeRun base Nat [] () captures (located 10 (symbol 7))
      (world.native ∅) (generator captures) conflictingProgram [picked, selection] := by
  intro run
  exact no_source_program_with_the_conflicting_second_read
    (run.to_source world (generator captures) (Equivalent.refl world (generator captures)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSequenceControls
