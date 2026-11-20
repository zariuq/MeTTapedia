import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.Events
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.Scope

/-!
# Live executions beside a concrete inconsistent world

The positive controls use the candidate's admitted import of a closed row.
There is a real firing on the live side, so the event/run equivalences are
exercised beyond two idle systems. The inconsistent publisher is the actual
state whose knowledge equates the distinct constants one and two.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.Controls

open RuleSyntax RuleSyntax.Worlds
open RuleSyntax.Examples (Tm X E c)
open RuleSyntax.Worlds.Controls (fiveRow emptyReader deadPublisher deadPublisher_dead)
open EventMultiplicity
open Mettapedia.GSLT.IndexedOperational

abbrev liveProgram : Program Tm := (∅ : Program Tm) ∪ {fiveRow}

def liveRun : (step X Nat E liveProgram).toStep.Run emptyReader :=
  .cons isolatedImport isolatedImport_admitted (.nil _)

theorem liveRun_length : liveRun.word.length = 1 := rfl

theorem singleton_import_path :
    ∃ path : ExecutionPath (firings (O := Nat) X E) sharedReader sharedResult, path.length = 1 :=
  ⟨singletonRunPath X E ∅ {fiveRow} liveRun, rfl⟩

def liveBesideDead :
    (asynchronous (events X Nat E liveProgram) (events X Nat E ∅)).Execution 1
      (emptyReader, deadPublisher) :=
  ⟨.inl ⟨isolatedImport, isolatedImport_admitted⟩, PUnit.unit⟩

/-- The mapped object is an actual admitted firing run: count, endpoint
and rule label all retain the live import. -/
theorem dead_beside_keeps_live_run :
    let run := deadExecutionRunEquiv X E liveProgram ∅ emptyReader deadPublisher
      deadPublisher_dead 1 liveBesideDead
    run.val.word.length = 1 ∧ run.val.last = isolatedImport.result X emptyReader ∧
      run.val.word.map (fun entry => entry.2.rule) = [fiveRow] := by
  refine ⟨(deadExecutionRunEquiv X E liveProgram ∅ emptyReader deadPublisher
    deadPublisher_dead 1 liveBesideDead).property, ?_, ?_⟩
  · exact deadExecutionRun_endpoint X E liveProgram ∅ emptyReader deadPublisher
      deadPublisher_dead 1 liveBesideDead
  · exact deadExecutionRun_word X E liveProgram ∅ emptyReader deadPublisher
      deadPublisher_dead 1 liveBesideDead

/-- A published row carrying contradictory knowledge changes no event of
the real live run, despite enlarging the shared rule set. -/
theorem dead_snapshot_keeps_live_run :
    let run := deadRowRunEquiv X E ∅ {fiveRow} deadPublisher (c 7) deadPublisher_dead
      emptyReader 1 ⟨liveRun, liveRun_length⟩
    run.val.word.length = 1 ∧ run.val.last = liveRun.last ∧
      run.val.word.map (fun entry => entry.2.rule) = [fiveRow] := by
  refine ⟨(deadRowRunEquiv X E ∅ {fiveRow} deadPublisher (c 7) deadPublisher_dead
    emptyReader 1 ⟨liveRun, liveRun_length⟩).property, ?_, ?_⟩
  · exact deadRowRun_endpoint X E ∅ {fiveRow} deadPublisher (c 7) deadPublisher_dead
      emptyReader 1 ⟨liveRun, liveRun_length⟩
  · exact deadRowRun_word X E ∅ {fiveRow} deadPublisher (c 7) deadPublisher_dead
      emptyReader 1 ⟨liveRun, liveRun_length⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.Controls.dead_beside_keeps_live_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.Controls.dead_snapshot_keeps_live_run
