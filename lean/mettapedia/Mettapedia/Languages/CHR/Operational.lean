import Mettapedia.Languages.CHR.Syntax
import Mathlib.Data.List.Perm.Basic

/-! Ground CHR's refined operational relation. Constraint occurrences, rule
occurrences, and propagation keys are distinct data. The relation does not
invoke a search procedure. Body goals run before a retained active constraint
continues, and a body may remove an occurrence whose continuation is parked.

Partner selection is nondeterministic within one rule occurrence. A concrete
executor's partner-selection order is a further realization choice. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR

structure Occurrence where
  id : Nat
  constraint : Constraint
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure Key where
  rule : Nat
  heads : List Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Task where
  | goals (environment : Environment) (goals : List Goal)
  | scan (active : Nat) (cursor : Nat)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

inductive Status where
  | running
  | failed
  | fault (reason : ArithmeticFault)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

structure State where
  tasks : List Task
  store : List Occurrence
  history : List Key
  nextId : Nat
  status : Status
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Constraint.asHead (constraint : Constraint) : Head :=
  ⟨constraint.name, constraint.arguments.map Term.value⟩

def initial (constraints : List Constraint) : State :=
  ⟨[.goals [] (constraints.map (Goal.tell ∘ Constraint.asHead))], [], [], 0, .running⟩

def State.WellFormed (state : State) : Prop :=
  (state.store.map Occurrence.id).Nodup ∧ ∀ occurrence ∈ state.store, occurrence.id < state.nextId

def guardsEval (environment : Environment) : List Guard → Except ArithmeticFault Bool
  | [] => .ok true
  | guard :: guards => do
      if ← guard.eval environment then guardsEval environment guards else pure false

/-- The head's ordered selections together with the unselected store.
The decomposition is a permutation, not set equality. -/
structure Selection where
  kept : List Occurrence
  removed : List Occurrence
  rest : List Occurrence
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def Selection.heads (selection : Selection) : List Occurrence := selection.kept ++ selection.removed
def Selection.key (selection : Selection) (ruleIndex : Nat) : Key :=
  ⟨ruleIndex, selection.heads.map Occurrence.id⟩

def Selection.Matches (selection : Selection) (rule : Rule) (environment : Environment)
    (store : List Occurrence) : Prop :=
  store.Perm (selection.kept ++ selection.removed ++ selection.rest) ∧
    (selection.heads.map Occurrence.id).Nodup ∧
    List.Forall₂ (fun head occurrence => head.instantiate environment = some occurrence.constraint)
      rule.kept selection.kept ∧
    List.Forall₂ (fun head occurrence => head.instantiate environment = some occurrence.constraint)
      rule.removed selection.removed ∧
    (environment.map Prod.fst).Nodup ∧
    ∀ binding ∈ environment, binding.1 ∈ rule.variables

/-- An active constraint occupies this head position. -/
def Selection.ActiveAt (selection : Selection) (active headIndex : Nat) : Prop :=
  ∃ occurrence, selection.heads[headIndex]? = some occurrence ∧ occurrence.id = active

def Selection.Fresh (selection : Selection) (rule : Rule) (ruleIndex : Nat) (history : List Key) : Prop :=
  rule.removed = [] → selection.key ruleIndex ∉ history

def commit (state : State) (rule : Rule) (ruleIndex : Nat) (environment : Environment)
    (selection : Selection) (active cursor : Nat) (tail : List Task) : State :=
  { state with
    store := selection.kept ++ selection.rest
    history := if rule.removed.isEmpty then selection.key ruleIndex :: state.history else state.history
    tasks := .goals environment rule.body ::
      (if selection.removed.any (fun occurrence => occurrence.id == active) then tail else .scan active cursor :: tail) }

/-- Refined steps: activate, scan in authored occurrence order, commit,
execute the body, and continue only while the active occurrence survives. -/
inductive Step (program : Program) : State → State → Prop
  | endGoals (state : State) (environment : Environment) (tail : List Task)
      (tasks : state.tasks = .goals environment [] :: tail) (running : state.status = .running) :
      Step program state { state with tasks := tail }
  | introduce (state : State) (environment : Environment) (head : Head) (goals : List Goal)
      (tail : List Task) (constraint : Constraint)
      (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
      (running : state.status = .running) (grounded : head.instantiate environment = some constraint) :
      Step program state { state with
        tasks := .scan state.nextId 0 :: .goals environment goals :: tail
        store := state.store ++ [⟨state.nextId, constraint⟩]
        nextId := state.nextId + 1 }
  | tellFault (state : State) (environment : Environment) (head : Head) (goals : List Goal) (tail : List Task)
      (tasks : state.tasks = .goals environment (.tell head :: goals) :: tail)
      (running : state.status = .running) (ungrounded : head.instantiate environment = none) :
      Step program state { state with status := .fault (.uninstantiated (.tuple head.arguments)) }
  | assign (state : State) (environment : Environment) (index : Nat) (expression : IntExpr)
      (goals : List Goal) (tail : List Task) (result : Int)
      (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
      (running : state.status = .running) (evaluated : expression.eval environment = .ok result)
      (compatible : lookup environment index = none ∨ lookup environment index = some (.integer result)) :
      Step program state { state with tasks := .goals ((index, .integer result) :: environment) goals :: tail }
  | assignFailed (state : State) (environment : Environment) (index : Nat) (expression : IntExpr)
      (goals : List Goal) (tail : List Task) (result : Int) (old : Value)
      (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
      (running : state.status = .running) (evaluated : expression.eval environment = .ok result)
      (bound : lookup environment index = some old) (different : old ≠ .integer result) :
      Step program state { state with status := .failed }
  | assignFault (state : State) (environment : Environment) (index : Nat) (expression : IntExpr)
      (goals : List Goal) (tail : List Task) (reason : ArithmeticFault)
      (tasks : state.tasks = .goals environment (.assign index expression :: goals) :: tail)
      (running : state.status = .running) (evaluated : expression.eval environment = .error reason) :
      Step program state { state with status := .fault reason }
  | fail (state : State) (environment : Environment) (goals : List Goal) (tail : List Task)
      (tasks : state.tasks = .goals environment (.fail :: goals) :: tail) (running : state.status = .running) :
      Step program state { state with status := .failed }
  | missingActive (state : State) (active cursor : Nat) (tail : List Task)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (missing : ∀ occurrence ∈ state.store, occurrence.id ≠ active) :
      Step program state { state with tasks := tail }
  | endScan (state : State) (active cursor : Nat) (tail : List Task)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (finished : (occurrences program)[cursor]? = none) :
      Step program state { state with tasks := tail }
  | skip (state : State) (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence) (rule : Rule)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (atCursor : (occurrences program)[cursor]? = some occurrence) (atRule : program.rules[occurrence.rule]? = some rule)
      (unusable : ∀ (environment : Environment) (selection : Selection),
        selection.Matches rule environment state.store → selection.ActiveAt active occurrence.head →
        ¬ selection.Fresh rule occurrence.rule state.history ∨ guardsEval environment rule.guards = .ok false) :
      Step program state { state with tasks := .scan active (cursor + 1) :: tail }
  | fire (state : State) (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence) (rule : Rule)
      (environment : Environment) (selection : Selection)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (atCursor : (occurrences program)[cursor]? = some occurrence) (atRule : program.rules[occurrence.rule]? = some rule)
      (matched : selection.Matches rule environment state.store) (activeHead : selection.ActiveAt active occurrence.head)
      (fresh : selection.Fresh rule occurrence.rule state.history) (guarded : guardsEval environment rule.guards = .ok true) :
      Step program state (commit state rule occurrence.rule environment selection active cursor tail)
  | guardFault (state : State) (active cursor : Nat) (tail : List Task) (occurrence : RuleOccurrence) (rule : Rule)
      (environment : Environment) (selection : Selection) (reason : ArithmeticFault)
      (tasks : state.tasks = .scan active cursor :: tail) (running : state.status = .running)
      (atCursor : (occurrences program)[cursor]? = some occurrence) (atRule : program.rules[occurrence.rule]? = some rule)
      (matched : selection.Matches rule environment state.store) (activeHead : selection.ActiveAt active occurrence.head)
      (fresh : selection.Fresh rule occurrence.rule state.history)
      (fault : guardsEval environment rule.guards = .error reason) :
      Step program state { state with status := .fault reason }

inductive Outcome where
  | pending
  | completed (store : List Constraint)
  | failed
  | fault (reason : ArithmeticFault)
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq

def observe (state : State) : Outcome :=
  match state.status with
  | .failed => .failed
  | .fault reason => .fault reason
  | .running => if state.tasks.isEmpty then .completed (state.store.map Occurrence.constraint) else .pending

end Mettapedia.Languages.CHR
