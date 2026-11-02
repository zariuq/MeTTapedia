import Mettapedia.Languages.Erlang.PatternMatching
import Mettapedia.Languages.Erlang.Primitives

/-! Resumable sequential Core Erlang machine. This profile evaluates the
function before its arguments and gathers arguments/fields left to right.
The Core frontend must retain the explicit let sequencing emitted by erlc;
this choice is not asserted as every source Erlang evaluation order.

Actor operations suspend as explicit requests, so a sequential transition
cannot deliver a message or allocate a pid invisibly. Guard failure resumes
the next clause with its original environment. Ordinary body faults escape
the guard attempt. Source adequacy and the emitted realization are separate
obligations. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang

inductive Build where
  | values | tuple | cons
  | apply (function : Value)
  | primitive (operator : Primitive)
  | actor (operation : ActorOperation)
  deriving Repr, BEq

inductive Frame where
  | applyFunction (arguments : List Code) (environment : Environment)
  | letValues (arity : Nat) (body : Code) (environment : Environment)
  | sequence (second : Code) (environment : Environment)
  | gather (kind : Build) (remaining : List Code) (environment : Environment) (collectedRev : List Value)
  | caseArgument (clauses : List Clause) (environment : Environment)
  | guardResult (arguments : List Value) (remaining : List Clause) (body : Code)
      (bound outer : Environment)
  | matchFail
  deriving Repr, BEq

abbrev Continuation := List Frame

inductive ActorRequest where
  | self
  | spawn (function : Value)
  | send (receiver : Nat) (message : Value)
  | peekMessage | nextMessage | removeMessage | waitInfinity
  deriving Repr, BEq

inductive MachineState where
  | evaluate (reference : Code) (environment : Environment) (continuation : Continuation)
  | returned (values : List Value) (continuation : Continuation)
  | choose (arguments : List Value) (clauses : List Clause) (environment : Environment) (continuation : Continuation)
  | request (operation : ActorRequest) (continuation : Continuation)
  | halted (result : Result)
  deriving Repr, BEq

def oneValue (values : List Value) : Except InternalError Value := match values with
  | [value] => .ok value
  | _ => .error (.returnArity 1 values.length)

def guardActive (continuation : Continuation) : Bool := continuation.any fun frame => match frame with
  | .guardResult _ _ _ _ _ => true
  | _ => false

def acceptsGuard : List Value → Bool
  | [.literal (.atom "true")] => true
  | _ => false

def raiseFault (fault : Fault) : Continuation → MachineState
  | [] => .halted (.error fault)
  | .guardResult arguments rest _ _ outer :: continuation => .choose arguments rest outer continuation
  | _ :: continuation => raiseFault fault continuation

def applyClosure (program : Program) (function : Value) (arguments : List Value)
    (continuation : Continuation) : Except InternalError MachineState :=
  match function with
  | .closure arity reference captured =>
      if arity ≠ arguments.length then .ok (raiseFault (.badarity function arguments) continuation)
      else match reference with
      | .lambda code => match program.instruction? code with
        | some (.lambda expected body) =>
            if expected = arity then .ok (.evaluate body (extend captured arguments) continuation)
            else .error (.returnArity expected arity)
        | _ => .error (.missingCode code)
      | .recursive group slot => do
          let some (.letRecursive definitions _) := program.instruction? group
            | throw (.invalidRecursiveGroup group slot)
          let some definition := definitions[slot]? | throw (.invalidRecursiveGroup group slot)
          if definition.arity ≠ arity then throw (.invalidRecursiveGroup group slot)
          pure (.evaluate definition.body
            (extend (recursiveEnvironment group definitions captured) arguments) continuation)
  | _ => .ok (raiseFault (.badfun function) continuation)

def actorRequest (operation : ActorOperation) (arguments : List Value)
    (continuation : Continuation) : Except InternalError MachineState := do
  if guardActive continuation && operation != .self then throw .effectfulGuard
  let request : Except Fault ActorRequest := match operation, arguments with
    | .self, [] => .ok .self
    | .spawn, [function@(.closure 0 _ _)] => .ok (.spawn function)
    | .send, [.pid receiver, message] => .ok (.send receiver message)
    | .peekMessage, [] => .ok .peekMessage
    | .nextMessage, [] => .ok .nextMessage
    | .removeMessage, [] => .ok .removeMessage
    | .waitInfinity, [] => .ok .waitInfinity
    | _, _ => .error .badarg
  match request with
  | .ok request => pure (.request request continuation)
  | .error fault => pure (raiseFault fault continuation)

def finishBuild (program : Program) (kind : Build) (values : List Value)
    (continuation : Continuation) : Except InternalError MachineState := do
  match kind with
  | .values => pure (.returned values continuation)
  | .tuple => pure (.returned [.tuple values] continuation)
  | .cons => match values with
    | [head, tail] => pure (.returned [.cons head tail] continuation)
    | _ => throw (.returnArity 2 values.length)
  | .apply function => applyClosure program function values continuation
  | .primitive operator => match ← operator.eval values with
    | .ok value => pure (.returned [value] continuation)
    | .error fault => pure (raiseFault fault continuation)
  | .actor operation => actorRequest operation values continuation

def startArguments (program : Program) (kind : Build) (arguments : List Code)
    (environment : Environment) (continuation : Continuation) : Except InternalError MachineState :=
  match arguments with
  | [] => finishBuild program kind [] continuation
  | first :: rest => .ok (.evaluate first environment (.gather kind rest environment [] :: continuation))

def evaluateInstruction (program : Program) (reference : Code) (environment : Environment)
    (continuation : Continuation) : Except InternalError MachineState := do
  let some instruction := program.instruction? reference | throw (.missingCode reference)
  match instruction with
  | .literal value => pure (.returned [.literal value] continuation)
  | .variable index => match environment[index]? with
    | some value => pure (.returned [value] continuation)
    | none => throw (.unboundVariable index)
  | .lambda arity _ => pure (.returned [.closure arity (.lambda reference) environment] continuation)
  | .apply function arguments =>
      pure (.evaluate function environment (.applyFunction arguments environment :: continuation))
  | .letValues arity argument body =>
      pure (.evaluate argument environment (.letValues arity body environment :: continuation))
  | .letRecursive definitions body =>
      pure (.evaluate body (recursiveEnvironment reference definitions environment) continuation)
  | .sequence first second => pure (.evaluate first environment (.sequence second environment :: continuation))
  | .values fields => startArguments program .values fields environment continuation
  | .tuple fields => startArguments program .tuple fields environment continuation
  | .cons head tail => startArguments program .cons [head, tail] environment continuation
  | .caseValues argument clauses =>
      pure (.evaluate argument environment (.caseArgument clauses environment :: continuation))
  | .primitive operator arguments => startArguments program (.primitive operator) arguments environment continuation
  | .actor operation arguments => startArguments program (.actor operation) arguments environment continuation
  | .matchFail reason => pure (.evaluate reason environment (.matchFail :: continuation))

def returnValues (program : Program) (values : List Value) : Continuation → Except InternalError MachineState
  | [] => .ok (.halted (.ok values))
  | frame :: continuation => do
      match frame with
      | .applyFunction arguments environment =>
          startArguments program (.apply (← oneValue values)) arguments environment continuation
      | .letValues arity body environment =>
          if values.length = arity then pure (.evaluate body (extend environment values) continuation)
          else throw (.returnArity arity values.length)
      | .sequence second environment => pure (.evaluate second environment continuation)
      | .gather kind remaining environment collectedRev =>
          let value ← oneValue values
          match remaining with
          | [] => finishBuild program kind (value :: collectedRev).reverse continuation
          | next :: rest => pure (.evaluate next environment
              (.gather kind rest environment (value :: collectedRev) :: continuation))
      | .caseArgument clauses environment => pure (.choose values clauses environment continuation)
      | .guardResult arguments rest body bound outer =>
          if acceptsGuard values then pure (.evaluate body bound continuation)
          else pure (.choose arguments rest outer continuation)
      | .matchFail => pure (raiseFault (.matchFail (← oneValue values)) continuation)

def chooseClause (arguments : List Value) (clauses : List Clause)
    (environment : Environment) (continuation : Continuation) : MachineState := match clauses with
  | [] => raiseFault (.caseClause arguments) continuation
  | clause :: rest => match matchFields environment clause.patterns arguments with
    | none => .choose arguments rest environment continuation
    | some bindings =>
        let bound := extend environment bindings
        .evaluate clause.guard bound (.guardResult arguments rest clause.body bound environment :: continuation)

def MachineState.step? (program : Program) : MachineState → Except InternalError (Option MachineState)
  | .evaluate reference environment continuation => do
      pure (some (← evaluateInstruction program reference environment continuation))
  | .returned values continuation => do pure (some (← returnValues program values continuation))
  | .choose arguments clauses environment continuation =>
      .ok (some (chooseClause arguments clauses environment continuation))
  | .request _ _ | .halted _ => .ok none

def begin (program : Program) : MachineState := .evaluate program.entry [] []

def advance (program : Program) : Nat → MachineState → Except InternalError MachineState
  | 0, state => .ok state
  | fuel + 1, state => match state.step? program with
      | .error error => .error error
      | .ok none => .ok state
      | .ok (some next) => advance program fuel next

theorem advance_add (program : Program) (first second : Nat) (state : MachineState) :
    advance program (first + second) state =
      (advance program first state).bind (advance program second) := by
  induction first generalizing state with
  | zero => simp [advance, Except.bind]
  | succ first ih =>
      simp only [Nat.succ_add, advance]
      cases step : state.step? program with
      | error error => rfl
      | ok next => cases next with
        | some next => exact ih next
        | none =>
            have fixed : ∀ fuel, advance program fuel state = .ok state := by
              intro fuel
              cases fuel <;> simp [advance, step]
            simp [fixed, Except.bind]

end Mettapedia.Languages.Erlang
