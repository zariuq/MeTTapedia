import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.Firings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Events

/-!
# Dead neighbours and closed rows preserve actual event executions

The candidate's event-fibre bijections compose with the existing equivalence
between event executions and native firing runs. A dead neighbour contributes
no event to the asynchronous firing system. Publishing a closed row from a
dead world preserves the exact run count, rule word and endpoint.

These statements concern firings. Full bag moves can still copy or publish
from a dead world, and that larger move relation needs its own observation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

open RuleSyntax RuleSyntax.Worlds
open EventMultiplicity
open Hosting.Alternatives.Worlds (snapshot)

universe uO uT uH uE uOcc

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O]
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)

def deadComparison (left right : Program Tm) :
    Bisimulation (asynchronous (events X O E left) (events X O E right)) (events X O E left)
      (fun pair state => pair.1 = state ∧ ¬ X.Solvable pair.2.knowledge) :=
  idleBeside (events X O E left) (events X O E right) (fun state => ¬ X.Solvable state.knowledge)
    (fun _ dead => dead_no_events right dead)

/-- The event bijection reaches counted, actual admitted runs. -/
noncomputable def deadExecutionRunEquiv (left right : Program Tm) (state deadState : State Tm O)
    (dead : ¬ X.Solvable deadState.knowledge) (count : Nat) :
    (asynchronous (events X O E left) (events X O E right)).Execution count (state, deadState) ≃
      {run : (step X O E left).toStep.Run state // run.word.length = count} :=
  ((deadComparison X E left right).executions count ⟨rfl, dead⟩).trans
    ((step X O E left).toStep.countedExecutionRunEquiv (fun {_} f => f.rule) state count)

theorem deadExecutionRun_endpoint (left right : Program Tm) (state deadState : State Tm O)
    (dead : ¬ X.Solvable deadState.knowledge) (count : Nat)
    (path : (asynchronous (events X O E left) (events X O E right)).Execution count (state, deadState)) :
    (deadExecutionRunEquiv X E left right state deadState dead count path).val.last =
      ((asynchronous (events X O E left) (events X O E right)).last path).1 := by
  have mapped := (deadComparison X E left right).execution_last ⟨rfl, dead⟩ path
  change ((step X O E left).toStep.runOfExecution (fun {_} f => f.rule)
    ((deadComparison X E left right).executions count ⟨rfl, dead⟩ path)).last = _
  rw [Interface.Step.runOfExecution_last]
  exact mapped.1.symm

theorem deadExecutionRun_word (left right : Program Tm) (state deadState : State Tm O)
    (dead : ¬ X.Solvable deadState.knowledge) (count : Nat)
    (path : (asynchronous (events X O E left) (events X O E right)).Execution count (state, deadState)) :
    (deadExecutionRunEquiv X E left right state deadState dead count path).val.word.map
        (fun entry => entry.2.rule) =
      (asynchronous (events X O E left) (events X O E right)).word path := by
  change ((step X O E left).toStep.runOfExecution (fun {_} f => f.rule)
    ((deadComparison X E left right).executions count ⟨rfl, dead⟩ path)).word.map _ = _
  exact ((step X O E left).toStep.runOfExecution_word _ _).trans
    ((deadComparison X E left right).execution_word ⟨rfl, dead⟩ path)

/-- The candidate's closed-row event realization composes through both
counted execution/run equivalences. It does not discard distinct firings. -/
noncomputable def deadRowRunEquiv (program shared : Program Tm) (publisher : State Tm O)
    (atom : Tm publisher.frame) (dead : ¬ X.Solvable publisher.knowledge)
    (reader : State Tm O) (count : Nat) :
    {run : (step X O E (program ∪ shared)).toStep.Run reader // run.word.length = count} ≃
      {run : (step X O E (program ∪ insert (snapshot publisher atom) shared)).toStep.Run reader //
        run.word.length = count} :=
  ((step X O E (program ∪ shared)).toStep.countedExecutionRunEquiv
      (fun {_} f => f.rule) reader count).symm.trans
    (((deadRowRealization (X := X) (E := E) program shared atom dead).bisimulation.executions count rfl).trans
      ((step X O E (program ∪ insert (snapshot publisher atom) shared)).toStep.countedExecutionRunEquiv
        (fun {_} f => f.rule) reader count))

theorem deadRowRun_endpoint (program shared : Program Tm) (publisher : State Tm O)
    (atom : Tm publisher.frame) (dead : ¬ X.Solvable publisher.knowledge)
    (reader : State Tm O) (count : Nat)
    (run : {run : (step X O E (program ∪ shared)).toStep.Run reader // run.word.length = count}) :
    (deadRowRunEquiv X E program shared publisher atom dead reader count run).val.last = run.val.last := by
  let source := (step X O E (program ∪ shared)).toStep
  let target := (step X O E (program ∪ insert (snapshot publisher atom) shared)).toStep
  let execution := (source.countedExecutionRunEquiv (fun {_} f => f.rule) reader count).symm run
  let bridge := (deadRowRealization (X := X) (E := E) program shared atom dead).bisimulation
  have restored : source.runOfExecution (fun {_} f => f.rule) execution = run.val :=
    congrArg Subtype.val ((source.countedExecutionRunEquiv (fun {_} f => f.rule) reader count).apply_symm_apply run)
  have endpoints := bridge.execution_last rfl execution
  change (target.runOfExecution (fun {_} f => f.rule) (bridge.executions count rfl execution)).last = _
  rw [Interface.Step.runOfExecution_last]
  change (events X O E (program ∪ shared)).last execution =
      (events X O E (program ∪ insert (snapshot publisher atom) shared)).last
        (bridge.executions count rfl execution) at endpoints
  rw [← endpoints, ← Interface.Step.runOfExecution_last, restored]

theorem deadRowRun_word (program shared : Program Tm) (publisher : State Tm O)
    (atom : Tm publisher.frame) (dead : ¬ X.Solvable publisher.knowledge)
    (reader : State Tm O) (count : Nat)
    (run : {run : (step X O E (program ∪ shared)).toStep.Run reader // run.word.length = count}) :
    (deadRowRunEquiv X E program shared publisher atom dead reader count run).val.word.map
        (fun entry => entry.2.rule) = run.val.word.map (fun entry => entry.2.rule) := by
  let source := (step X O E (program ∪ shared)).toStep
  let target := (step X O E (program ∪ insert (snapshot publisher atom) shared)).toStep
  let execution := (source.countedExecutionRunEquiv (fun {_} f => f.rule) reader count).symm run
  let bridge := (deadRowRealization (X := X) (E := E) program shared atom dead).bisimulation
  have restored : source.runOfExecution (fun {_} f => f.rule) execution = run.val :=
    congrArg Subtype.val ((source.countedExecutionRunEquiv (fun {_} f => f.rule) reader count).apply_symm_apply run)
  change (target.runOfExecution (fun {_} f => f.rule) (bridge.executions count rfl execution)).word.map _ = _
  have targetWord := target.runOfExecution_word (fun {_} f => f.rule) (bridge.executions count rfl execution)
  have sourceWord := source.runOfExecution_word (fun {_} f => f.rule) execution
  rw [restored] at sourceWord
  exact targetWord.trans ((bridge.execution_word rfl execution).trans sourceWord.symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.deadExecutionRunEquiv
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.deadExecutionRun_word
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.deadRowRun_endpoint
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.deadRowRun_word
