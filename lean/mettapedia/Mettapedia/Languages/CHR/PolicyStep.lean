import Mettapedia.Languages.CHR.PartnerSelection

/-! Refined steps under the declared partner policy. A rule occurrence fires
with, or faults at, a selection that no other matching, fresh selection not
rejected by its guards is newer than; every other step is the refined step.
The policy only removes choices the refined relation leaves open. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

/-- No selection that matches, is fresh and is not rejected by its guards is
newer than `selection`. -/
def NewestFirst (rule : Rule) (index head active : Nat) (store : List Occurrence) (history : List Key)
    (selection : Selection) : Prop :=
  ∀ (environment : Environment) (other : Selection), other.Matches rule environment store →
    other.ActiveAt active head → other.Fresh rule index history → guardsEval environment rule.guards ≠ .ok false →
    PartnerSelection.newerIds (other.heads.map Occurrence.id) (selection.heads.map Occurrence.id) = false

/-- Refined steps under the newest-first partner policy. -/
inductive PolicyStep (program : Program) : State → State → Prop
  | endGoals (state : State) (environment : Environment) (tail : List Task)
      (tasks : state.tasks = .goals environment [] :: tail) (running : state.status = .running) :
      PolicyStep program state { state with tasks := tail }
  | introduce (state : State) (environment : Environment) (head : Head) (goals : List Goal)
      (tail : List Task) (constraint : Constraint)
      (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
      (running : state.status = .running) (grounded : head.instantiate environment = some constraint) :
      PolicyStep program state { state with
        tasks := .scan state.nextId 0 :: .goals environment goals :: tail
        store := state.store ++ [⟨state.nextId, constraint⟩]
        nextId := state.nextId + 1 }
  | tellFault (state : State) (environment : Environment) (head : Head) (goals : List Goal) (tail : List Task)
      (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
      (running : state.status = .running) (ungrounded : head.instantiate environment = none) :
      PolicyStep program state { state with status := .fault (.uninstantiated (.tuple head.arguments)) }
  | assign (state : State) (environment : Environment) (index : Nat) (expression : IntExpr)
      (goals : List Goal) (tail : List Task) (result : Int)
      (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
      (running : state.status = .running) (evaluated : expression.eval environment = .ok result)
      (compatible : lookup environment index = none ∨ lookup environment index = some (.integer result)) :
      PolicyStep program state { state with tasks := .goals ((index, .integer result) :: environment) goals :: tail }
  | assignFailed (state : State) (environment : Environment) (index : Nat) (expression : IntExpr)
      (goals : List Goal) (tail : List Task) (result : Int) (old : Value)
      (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
      (running : state.status = .running) (evaluated : expression.eval environment = .ok result)
      (bound : lookup environment index = some old) (different : old ≠ .integer result) :
      PolicyStep program state { state with status := .failed }
  | assignFault (state : State) (environment : Environment) (index : Nat) (expression : IntExpr)
      (goals : List Goal) (tail : List Task) (reason : ArithmeticFault)
      (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
      (running : state.status = .running) (evaluated : expression.eval environment = .error reason) :
      PolicyStep program state { state with status := .fault reason }
  | fail (state : State) (environment : Environment) (goals : List Goal) (tail : List Task)
      (tasks : state.tasks = .goals environment (.fail :: goals) :: tail) (running : state.status = .running) :
      PolicyStep program state { state with status := .failed }
  | missingActive (state : State) (active cursor : Nat) (tail : List Task)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (missing : ∀ occurrence ∈ state.store, occurrence.id ≠ active) :
      PolicyStep program state { state with tasks := tail }
  | endScan (state : State) (active cursor : Nat) (tail : List Task)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (finished : (occurrences program)[cursor]? = none) :
      PolicyStep program state { state with tasks := tail }
  | skip (state : State) (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence) (rule : Rule)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (atCursor : (occurrences program)[cursor]? = some occurrence) (atRule : program.rules[occurrence.rule]? = some rule)
      (unusable : ∀ (environment : Environment) (selection : Selection),
        selection.Matches rule environment state.store → selection.ActiveAt active occurrence.head →
        ¬ selection.Fresh rule occurrence.rule state.history ∨ guardsEval environment rule.guards = .ok false) :
      PolicyStep program state { state with tasks := .scan active (cursor + 1) :: tail }
  | fire (state : State) (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence) (rule : Rule)
      (environment : Environment) (selection : Selection)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (atCursor : (occurrences program)[cursor]? = some occurrence) (atRule : program.rules[occurrence.rule]? = some rule)
      (matched : selection.Matches rule environment state.store) (activeHead : selection.ActiveAt active occurrence.head)
      (fresh : selection.Fresh rule occurrence.rule state.history) (guarded : guardsEval environment rule.guards = .ok true)
      (newest : NewestFirst rule occurrence.rule occurrence.head active state.store state.history selection) :
      PolicyStep program state (commit state rule occurrence.rule environment selection active cursor tail)
  | guardFault (state : State) (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence) (rule : Rule)
      (environment : Environment) (selection : Selection) (reason : ArithmeticFault)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (atCursor : (occurrences program)[cursor]? = some occurrence) (atRule : program.rules[occurrence.rule]? = some rule)
      (matched : selection.Matches rule environment state.store) (activeHead : selection.ActiveAt active occurrence.head)
      (fresh : selection.Fresh rule occurrence.rule state.history)
      (fault : guardsEval environment rule.guards = .error reason)
      (newest : NewestFirst rule occurrence.rule occurrence.head active state.store state.history selection) :
      PolicyStep program state { state with status := .fault reason }

/-- The policy only restricts the refined relation. -/
theorem PolicyStep.refined {program : Program} {state next : State} (step : PolicyStep program state next) :
    Step program state next := by
  cases step with
  | endGoals environment tail tasks running => exact .endGoals state environment tail tasks running
  | introduce environment head goals tail constraint tasks running grounded =>
    exact .introduce state environment head goals tail constraint tasks running grounded
  | tellFault environment head goals tail tasks running ungrounded =>
    exact .tellFault state environment head goals tail tasks running ungrounded
  | assign environment index expression goals tail result tasks running evaluated compatible =>
    exact .assign state environment index expression goals tail result tasks running evaluated compatible
  | assignFailed environment index expression goals tail result old tasks running evaluated bound different =>
    exact .assignFailed state environment index expression goals tail result old tasks running evaluated bound different
  | assignFault environment index expression goals tail reason tasks running evaluated =>
    exact .assignFault state environment index expression goals tail reason tasks running evaluated
  | fail environment goals tail tasks running => exact .fail state environment goals tail tasks running
  | missingActive active cursor tail tasks running missing =>
    exact .missingActive state active cursor tail tasks running missing
  | endScan active cursor tail tasks running finished => exact .endScan state active cursor tail tasks running finished
  | skip active cursor tail occurrence rule tasks running atCursor atRule unusable =>
    exact .skip state active cursor tail occurrence rule tasks running atCursor atRule unusable
  | fire active cursor tail occurrence rule environment selection tasks running atCursor atRule matched activeHead fresh
      guarded _ =>
    exact .fire state active cursor tail occurrence rule environment selection tasks running atCursor atRule matched
      activeHead fresh guarded
  | guardFault active cursor tail occurrence rule environment selection reason tasks running atCursor atRule matched
      activeHead fresh fault _ =>
    exact .guardFault state active cursor tail occurrence rule environment selection reason tasks running atCursor atRule
      matched activeHead fresh fault

theorem PolicyStep.runs_refined {program : Program} {state final : State}
    (run : Relation.ReflTransGen (PolicyStep program) state final) : Relation.ReflTransGen (Step program) state final := by
  induction run with
  | refl => exact .refl
  | tail _ step reached => exact reached.tail step.refined

#print axioms PolicyStep.runs_refined

end Mettapedia.Languages.CHR
