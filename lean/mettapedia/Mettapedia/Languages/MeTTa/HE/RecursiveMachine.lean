import Mettapedia.Languages.MeTTa.HE.RecursiveTasks
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.OSLF.Framework.DerivedModalities

/-!
# Retained control and contextual HE transition rules

Each advance enters one request or consumes one first-order continuation.
Recursive evaluator calls become retained requests. Selected head values and
their bindings are used by the remaining branch without evaluating that head
again. Matching, type checks and grounded dispatch retain their own coarser
granularity. The executable profile drains an internal ordered enumeration.
The contextual machine takes its lookup contract separately; HE completion is
observed as a bag with multiplicity. Internal drain order is not a promised
language-level answer order.

This is a first-order Atom profile of HE. It does not define MeTTa as a whole
or constrain HO MeTTa Prime's binders, typed contexts, or search strategies.
-/

open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory (aliasConstraints)

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open RecursiveTasks
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Expansion does not call any of the six recursive evaluator functions. -/
def enter (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (lookup : TypeLookup := rawTypeLookup space) : Control × List Frame :=
  match task with
  | .atom _ _ _ 0 _ => (.returning [], [])
  | .atom value expected bindings (n + 1) live =>
      if isEmptyOrError value then (.returning [(value, bindings)], [])
      else if expected == Atom.atomType || expected == getMetaType value ||
          getMetaType value == Atom.variableType then (.returning [(value, bindings)], [])
      else if getMetaType value == Atom.symbolType || getMetaType value == Atom.groundedType ||
          value == Atom.unit then (.returning (typeCast value expected space bindings n lookup), [])
      else if getMetaType value == Atom.expressionType then
        (.work (.expression value expected bindings n live), [.filter])
      else (.returning [(value, bindings)], [])
  | .expression _ _ _ 0 _ => (.returning [], [])
  | .expression value expected bindings (n + 1) live =>
      match value with
      | .expression (operator :: _) =>
          let types := lookup bindings operator expected
          let continuation :=
            if types.any (fun type => !isFunctionType type || type == Atom.undefinedType)
            then Frame.append (.tupleCalls value expected bindings n live)
            else .fallback value expected bindings n types
          (.work (.functions value expected bindings n types live), [continuation])
      | _ => (.returning [], [])
  | .func _ _ _ 0 _ => (.returning [], [])
  | .func value operatorType bindings (n + 1) live =>
      match value with
      | .expression (operator :: arguments) =>
          (.work (.atom operator operatorType bindings n (operatorType :: arguments ++ live)),
            [.heads operatorType arguments n live])
      | _ => (.returning [], [])
  | .args _ _ _ 0 _ => (.returning [], [])
  | .args values types bindings (n + 1) live =>
      match values, types with
      | [], [] => (.returning [(argumentPacket [], bindings)], [])
      | value :: remaining, type :: remainingTypes =>
          (.work (.atom value type bindings n (remaining ++ remainingTypes ++ live)),
            [.argumentHeads value remaining remainingTypes n live])
      | _, _ => (.returning [], [])
  | .tuple _ _ 0 _ => (.returning [], [])
  | .tuple value bindings (n + 1) live =>
      match value with
      | .expression [] => (.returning [(Atom.unit, bindings)], [])
      | .expression [single] =>
          (.work (.atom single Atom.undefinedType bindings n live), [.tupleSingleton])
      | .expression (head :: second :: remaining) =>
          (.work (.atom head Atom.undefinedType bindings n
              (.expression (second :: remaining) :: live)),
            [.tupleHeads (.expression (second :: remaining)) n live])
      | _ => (.returning [], [])
  | .call value expected bindings fuel live =>
      (.work (.invocation (.ordinary expected) value bindings fuel live), [])
  | .functions _ _ _ _ [] _ => (.returning [], [])
  | .functions value expected bindings fuel (operatorType :: remaining) live =>
      let rest := Frame.append (.functions value expected bindings fuel remaining live)
      if isFunctionType operatorType then
        match checkIfFunctionTypeIsApplicable value operatorType expected space bindings fuel lookup with
        | .inl _ => (.returning [], [rest])
        | .inr alternatives =>
            (.work (.bindingAlternatives value operatorType (resultType operatorType) fuel
              alternatives live), [rest])
      else (.returning [], [rest])
  | .bindingAlternatives _ _ _ _ [] _ => (.returning [], [])
  | .bindingAlternatives value operatorType expected fuel (selected :: remaining) live =>
      (.work (.func value operatorType selected fuel (expected :: live)),
        [.calls expected fuel live,
          .append (.bindingAlternatives value operatorType expected fuel remaining live)])
  | .heads _ _ _ [] _ => (.returning [], [])
  | .heads operatorType arguments fuel ((head, selected) :: remaining) live =>
      let rest := Frame.append (.heads operatorType arguments fuel remaining live)
      if isEmptyOrError head then (.returning [(head, selected)], [rest])
      else match getFunctionArgTypes operatorType with
        | none => (.returning [], [rest])
        | some types =>
            (.work (.args arguments types selected fuel (head :: live)), [.functionTail head, rest])
  | .argumentHeads _ _ _ _ [] _ => (.returning [], [])
  | .argumentHeads original remaining types fuel ((head, selected) :: alternatives) live =>
      let rest := Frame.append (.argumentHeads original remaining types fuel alternatives live)
      if head != original && isEmptyOrError head then (.returning [(head, selected)], [rest])
      else (.work (.args remaining types selected fuel (head :: live)), [.argumentTail head, rest])
  | .tupleHeads _ _ [] _ => (.returning [], [])
  | .tupleHeads tail fuel ((head, selected) :: remaining) live =>
      let rest := Frame.append (.tupleHeads tail fuel remaining live)
      if isEmptyOrError head then (.returning [(head, selected)], [rest])
      else (.work (.tuple tail selected fuel (head :: live)), [.tupleTail head, rest])
  | .calls _ _ [] _ => (.returning [], [])
  | .calls expected fuel ((value, bindings) :: remaining) live =>
      (.work (.call value expected bindings fuel live),
        [.append (.calls expected fuel remaining live)])
  | .atoms _ _ [] _ => (.returning [], [])
  | .atoms expected fuel ((value, bindings) :: remaining) live =>
      (.work (.atom value expected bindings fuel live),
        [.append (.atoms expected fuel remaining live)])
  | .returned original value expected bindings fuel live =>
      if value == Atom.notReducible then (.returning [(original, bindings)], [])
      else if isEmptyOrError value then (.returning [(value, bindings)], [])
      else (.work (.atom value expected bindings fuel live), [])
  | .returns _ _ _ [] _ => (.returning [], [])
  | .returns original expected fuel ((value, bindings) :: remaining) live =>
      (.work (.returned original value expected bindings fuel live),
        [.append (.returns original expected fuel remaining live)])
  | .equations _ _ _ _ [] _ => (.returning [], [])
  | .equations original expected incoming fuel ((rhs, selected) :: remaining) live =>
      let alternatives := (mergeBindings selected (aliasConstraints incoming) fuel).filterMap fun merged =>
        if merged.hasLoop then none else some (merged.applyFull rhs fuel, merged)
      (.returning alternatives,
        [.append (.equations original expected incoming fuel remaining live)])
  | .grounded _ _ _ _ [] _ => (.returning [], [])
  | .grounded original expected incoming fuel ((value, selected) :: remaining) live =>
      (.returning ((mergeBindings selected incoming fuel).map fun merged =>
          (merged.applyFull value fuel, merged)),
        [.append (.grounded original expected incoming fuel remaining live)])
  | .tupleCalls value expected bindings fuel live =>
      (.work (.tuple value bindings fuel (expected :: live)), [.calls expected fuel live])
  | .invocation _ _ _ 0 _ _ => (.returning [], [])
  | .invocation mode value bindings (n + 1) live caller =>
      if mode.errorPassthrough value then
        (.returning [(value, bindings)], [])
      else match value with
      | .expression (operator :: arguments) =>
        if dispatch.isExecutable operator then
          match dispatch.execute operator arguments with
          | .ok results =>
              (.work (.grounded value mode.expected bindings n results live),
                [.producerResults mode value bindings n live Atom.empty])
          | .runtimeError message =>
              (.returning [(Atom.error value (.symbol message), bindings)],
                [.invocationReturn mode value n live])
          | .noReduce | .incorrectArgument =>
              (.returning [(Atom.notReducible, bindings)], [.invocationReturn mode value n live])
        else if minimalInstruction value then
          (.work (.minimal value bindings n (mode.pendingScope live) caller),
            [.invocationReturn mode value n live])
        else
          (.work (.equations value mode.expected bindings n
            (queryEquationsAvoiding (equationScope live value mode.expected bindings) space value n) live),
              [.producerResults mode value bindings n live Atom.notReducible])
      | _ =>
          (.work (.equations value mode.expected bindings n
            (queryEquationsAvoiding (equationScope live value mode.expected bindings) space value n) live),
              [.producerResults mode value bindings n live Atom.notReducible])
  | .produced _ _ 0 _ _ _ => (.returning [], [])
  | .produced value bindings (n + 1) live caller provenance =>
      if provenance == .completed then (.returning [(value, bindings)], []) else
      match value with
      | .expression [.symbol "function", _] => (.work (.primitive value bindings n live caller), [])
      | _ => (.returning [(value, bindings)], [])
  | .productions _ [] _ _ _ => (.returning [], [])
  | .productions fuel ((value, bindings) :: remaining) live caller provenance =>
      (.work (.produced value bindings fuel live caller provenance),
        [.append (.productions fuel remaining live caller provenance)])
  | .minimal _ _ 0 _ _ => (.returning [], [])
  | .minimal value bindings (n + 1) live caller =>
      if minimalInstruction value then
        match value with
        | .expression (.symbol "chain" :: _) =>
            (.work (.primitive value bindings n live caller), [.minimalResults n live caller])
        | _ => (.work (.primitive value bindings n live caller), [])
      else (.returning [(value, bindings)], [])
  | .minimals _ [] _ _ => (.returning [], [])
  | .minimals fuel ((value, bindings) :: remaining) live caller =>
      (.work (.minimal value bindings fuel live caller), [.append (.minimals fuel remaining live caller)])
  | .primitive _ _ 0 _ _ => (.returning [], [])
  | .primitive value bindings (n + 1) live caller =>
      match value with
      | .expression [.symbol "eval", atom] =>
          (.work (.invocation .raw (bindings.applyFull atom n) bindings n live caller), [])
      | .expression [.symbol "chain", atom, .var name, template] =>
          (.work (.minimal atom bindings n (value :: live) (some value)),
            [.chainResults name template n])
      | .expression [.symbol "unify", target, pattern, yes, no] =>
          let results := unifySuccessResults target pattern yes bindings n
          (.returning (if results.isEmpty then [(no, bindings)] else results), [])
      | .expression (.symbol "unify" :: _) => (.returning [(mkUnifyBadArityError value, bindings)], [])
      | .expression [.symbol "cons-atom", head, .expression tail] =>
          (.returning [(.expression (head :: tail), bindings)], [])
      | .expression [.symbol "decons-atom", .expression (head :: tail)] =>
          (.returning [(.expression [head, .expression tail], bindings)], [])
      | .expression [.symbol "function", body@(.expression _)] =>
          (.work (.functionBody body bindings n (value :: live) (some value)),
            [.functionTerminal caller])
      | _ => (.returning [], [])
  | .chainRows _ _ _ [] => (.returning [], [])
  | .chainRows name template fuel ((value, bindings) :: remaining) =>
      (.returning [(chainSubstitute name (bindings.applyFull value fuel) template, bindings)],
        [.append (.chainRows name template fuel remaining)])
  | .functionBody _ _ 0 _ _ => (.returning [], [])
  | .functionBody value bindings (n + 1) live caller =>
      (.work (.minimal value bindings n live caller), [.bodyResults n live caller])
  | .bodyResults _ [] _ _ => (.returning [], [])
  | .bodyResults fuel ((value, bindings) :: remaining) live caller =>
      let materialized := bindings.applyFull value fuel
      let rest := Frame.append (.bodyResults fuel remaining live caller)
      if minimalInstruction materialized then
        (.work (.functionBody materialized bindings fuel live caller), [rest])
      else (.returning [(materialized, bindings)], [rest])
  | .producerResults mode original incoming fuel live emptyReply results =>
      let returned := Frame.invocationReturn mode original fuel live
      if results.isEmpty then (.returning [(emptyReply, incoming)], [returned])
      else (.work (.productions fuel results (mode.pendingScope live) (some original)), [returned])
  | .completed value expected bindings fuel =>
      (.returning (completedCallReturn space value expected bindings fuel lookup), [])

def resume (space : Space) (frame : Frame) (results : ResultSet)
    (lookup : TypeLookup := rawTypeLookup space) : Control × List Frame :=
  match frame with
  | .filter => (.returning (successPriority results), [])
  | .heads operatorType arguments fuel live =>
      (.work (.heads operatorType arguments fuel results live), [])
  | .argumentHeads original remaining types fuel live =>
      (.work (.argumentHeads original remaining types fuel results live), [])
  | .tupleHeads tail fuel live => (.work (.tupleHeads tail fuel results live), [])
  | .calls expected fuel live => (.work (.calls expected fuel results live), [])
  | .functionTail head => (.returning (RecursiveTasks.functionTail head results), [])
  | .argumentTail head => (.returning (RecursiveTasks.argumentTail head results), [])
  | .tupleSingleton => (.returning (results.map HE.tupleSingleton), [])
  | .tupleTail head => (.returning (RecursiveTasks.tupleTail head results), [])
  | .append remaining => (.work remaining, [.prepend results])
  | .prepend selected => (.returning (selected ++ results), [])
  | .fallback value expected bindings fuel types =>
      (.returning (functionFallback space value expected bindings fuel types results lookup), [])
  | .invocationReturn mode original fuel live =>
      match mode with
      | .raw => (.returning results, [])
      | .ordinary expected => (.work (.returns original expected fuel results live), [])
  | .producerResults mode original incoming fuel live emptyReply =>
      (.work (.producerResults mode original incoming fuel live emptyReply results), [])
  | .minimalResults fuel live caller => (.work (.minimals fuel results live caller), [])
  | .chainResults name template fuel => (.work (.chainRows name template fuel results), [])
  | .functionTerminal caller =>
      (.returning (results.map fun (value, bindings) => (HE.functionTerminal caller value, bindings)), [])
  | .bodyResults fuel live caller => (.work (.bodyResults fuel results live caller), [])

/-- One internal advance, retaining the surrounding continuation and history. -/
def next (dispatch : GroundedDispatch) (state : Configuration) : Option Configuration :=
  match state.control, state.stack with
  | .work task, stack =>
      let entered := enter state.space dispatch task
      some {state with control := entered.1, stack := entered.2 ++ stack}
  | .returning results, frame :: remaining =>
      let resumed := resume state.space frame results
      some {state with control := resumed.1, stack := resumed.2 ++ remaining}
  | .returning _, [] => none

/-- Execute the finite-depth approximation and drain each occurrence once.
An empty approximation is not evidence of completed source-level failure; use
`Checked.machine` when a caller must distinguish exhaustion from completion. -/
def machine (dispatch : GroundedDispatch) : Machine Configuration ResultPair Configuration Empty where
  step state :=
    match next dispatch state with
    | some after => some (.silent after)
    | none => match state.control with
      | .work _ => none
      | .returning [] => some (.finish state)
      | .returning (result :: remaining) =>
          let saved := {state with
            control := .returning remaining
            emitted := state.emitted ++ [result]}
          some (.publish [result] saved)

theorem resume_prefix (dispatch : GroundedDispatch) (state saved : Configuration)
    (first second : Nat) (observed : ResultSet)
    (paused : ((machine dispatch).run first state) = (observed, .exhausted saved)) :
    (machine dispatch).run (first + second) state =
      (observed ++ ((machine dispatch).run second saved).1,
        ((machine dispatch).run second saved).2) :=
  (machine dispatch).established_and_pending first second state saved observed paused

/-! ## Resource-checked retained execution

The earlier machine realizes a finite evaluator approximation. This interface
checks every bounded leaf before consuming its reply. Insufficient evaluator
or leaf depth suspends the retained request; it is never an empty answer.
-/

namespace Checked

inductive ResourceRequest where
  | evaluationDepth
  | leafDepth
  | primitiveService (instruction : Atom)
  deriving DecidableEq, Repr

/-- All bounded operations which this request will execute have coverage.
Recursive evaluator calls are checked when their own retained request is entered. -/
def taskReady (space : Space) (dispatch : GroundedDispatch) (task : Task)
    (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  match task with
  | .atom _ _ _ 0 _ | .expression _ _ _ 0 _ | .func _ _ _ 0 _
  | .args _ _ _ 0 _ | .tuple _ _ 0 _
  | .invocation _ _ _ 0 _ _ | .produced _ _ 0 _ _ _ | .minimal _ _ 0 _ _
  | .primitive _ _ 0 _ _ | .functionBody _ _ 0 _ _ => false
  | .atom value expected bindings (depth + 1) _ =>
      if isEmptyOrError value then true
      else if expected == Atom.atomType || expected == getMetaType value ||
          getMetaType value == Atom.variableType then true
      else if getMetaType value == Atom.symbolType || getMetaType value == Atom.groundedType ||
          value == Atom.unit then typeCastCovered value expected space bindings depth lookup
      else true
  | .invocation mode value bindings (depth + 1) live _ =>
      if mode.errorPassthrough value then true
      else match value with
      | .expression (operator :: _) =>
          if dispatch.isExecutable operator then true
          else if minimalInstruction value then true
          else queryEquationsCovered (equationScope live value mode.expected bindings) space value depth
      | _ => queryEquationsCovered (equationScope live value mode.expected bindings) space value depth
  | .primitive value bindings (depth + 1) _ _ =>
      if minimalCoreSupported value then
        match value with
        | .expression [.symbol "eval", atom] => bindings.applyFullCovered atom depth
        | .expression [.symbol "unify", target, pattern, _, _] =>
            unifyMatchesCovered target pattern bindings depth
        | _ => true
      else false
  | .functions value expected bindings depth (operatorType :: _) _ =>
      if isFunctionType operatorType then
        functionTypeCovered value operatorType expected space bindings depth lookup
      else true
  | .equations _ _ incoming depth ((rhs, selected) :: _) _ =>
      matchCovered depth (.merge selected (aliasConstraints incoming)) &&
        (mergeBindings selected (aliasConstraints incoming) depth).all fun merged =>
          (merged.hasLoop || merged.applyFullCovered rhs depth)
  | .grounded _ _ incoming depth ((value, selected) :: _) _ =>
      matchCovered depth (.merge selected incoming) &&
        (mergeBindings selected incoming depth).all fun merged => merged.applyFullCovered value depth
  | .chainRows _ _ depth ((value, bindings) :: _)
  | .bodyResults depth ((value, bindings) :: _) _ _ => bindings.applyFullCovered value depth
  | .completed value expected bindings depth =>
      if isEmptyOrError value || expected == Atom.undefinedType || expected == Atom.atomType ||
          expected == getMetaType value || getMetaType value == Atom.variableType then true
      else typeCastCovered value expected space bindings depth lookup
  | _ => true

/-- The fallback frame repeats applicability queries only when all preceding
function alternatives failed. Those negative queries need coverage too. -/
def frameReady (space : Space) (results : ResultSet) (frame : Frame)
    (lookup : TypeLookup := rawTypeLookup space) : Bool :=
  match frame with
  | .fallback value expected bindings depth types =>
      !results.isEmpty || types.all fun operatorType =>
        !isFunctionType operatorType ||
          functionTypeCovered value operatorType expected space bindings depth lookup
  | _ => true

def blocked (dispatch : GroundedDispatch) (state : Configuration) : Option ResourceRequest :=
  match state.control, state.stack with
  | .work task, _ =>
      if taskReady state.space dispatch task then none
      else some (match task with
        | .primitive value _ (_ + 1) _ _ =>
            if minimalCoreSupported value then .leafDepth else .primitiveService value
        | _ => if task.depth == 0 then .evaluationDepth else .leafDepth)
  | .returning results, frame :: _ =>
      if frameReady state.space results frame then none else some .leafDepth
  | .returning _, [] => none

/-- Add resource suspension to an existing recursive worker. The complete
configuration is the request's retained receiver. -/
def guardMachine (base : Machine Configuration ResultPair Configuration Empty)
    (blocking : Configuration → Option ResourceRequest) :
    Machine Configuration ResultPair Configuration ResourceRequest where
  step state :=
    match blocking state with
    | some request => some (.call request state)
    | none => (base.step state).map (Transition.relabel id id Empty.elim)

/-- Every completed guarded run follows covered transitions. Any map that
commutes with those transitions preserves its full run and final receiver. -/
theorem guard_completed_map
    (base : Machine Configuration ResultPair Configuration Empty)
    (blocking : Configuration → Option ResourceRequest)
    (stateMap : Configuration → Configuration)
    (stepMap : ∀ state, blocking state = none →
      base.step (stateMap state) = (base.step state).map (fun transition =>
        (transition.mapState stateMap).relabel id stateMap id)) (budget : Nat)
    (state final : Configuration) (events : ResultSet)
    (completed : (guardMachine base blocking).run budget state = (events, .finished final)) :
    base.run budget (stateMap state) =
      (events, .finished (stateMap final)) := by
  induction budget generalizing state final events with
  | zero => simp [Machine.run] at completed
  | succ budget ih =>
      cases blockedHere : blocking state with
      | some request => simp [Machine.run, guardMachine, blockedHere] at completed
      | none =>
          have commute := stepMap state blockedHere
          cases stepped : base.step state with
          | none => simp [Machine.run, guardMachine, blockedHere, stepped] at completed
          | some transition =>
              have checkedStep : (guardMachine base blocking).step state =
                  some (transition.relabel id id Empty.elim) := by
                simp [guardMachine, blockedHere, stepped]
              cases transition with
              | silent next =>
                  have tail : (guardMachine base blocking).run budget next = (events, .finished final) := by
                    simpa only [Machine.run, checkedStep, Transition.relabel] using completed
                  have targetStep : base.step (stateMap state) =
                      some (.silent (stateMap next)) := by
                    rw [commute, stepped]
                    rfl
                  rw [Machine.run_succ_silent _ targetStep]
                  exact ih next final events tail
              | publish published next =>
                  rw [Machine.run_succ_publish _ checkedStep] at completed
                  cases later : (guardMachine base blocking).run budget next with
                  | mk remaining outcome =>
                      cases outcome with
                      | finished terminal =>
                          have same : published ++ remaining = events ∧ terminal = final := by
                            simpa only [later, Transition.relabel, Prod.fst, Prod.snd,
                              List.map_id, id_eq, Prod.mk.injEq, Outcome.finished.injEq] using completed
                          obtain ⟨rfl, rfl⟩ := same
                          have targetStep : base.step (stateMap state) =
                              some (.publish published (stateMap next)) := by
                            rw [commute, stepped]
                            simp [Transition.mapState, Transition.relabel]
                          rw [Machine.run_succ_publish _ targetStep, ih next terminal remaining later]
                      | faulted | suspended _ _ | stuck _ | exhausted _ => simp [later] at completed
              | finish terminal =>
                  have same : events = [] ∧ terminal = final := by
                    simpa only [Machine.run, checkedStep, Transition.relabel,
                      Prod.mk.injEq, Outcome.finished.injEq, id_eq, eq_comm] using completed
                  obtain ⟨rfl, rfl⟩ := same
                  have targetStep : base.step (stateMap state) =
                      some (.finish (stateMap terminal)) := by
                    rw [commute, stepped]
                    rfl
                  exact base.run_succ_finish targetStep
              | fail faults => simp [Machine.run, checkedStep, Transition.relabel] at completed
              | call request saved => exact request.elim

/-- In particular, the guard cannot invent a successful execution. -/
theorem guard_finished_refines
    (base : Machine Configuration ResultPair Configuration Empty)
    (blocking : Configuration → Option ResourceRequest)
    (budget : Nat) (state final : Configuration) (events : ResultSet)
    (completed : (guardMachine base blocking).run budget state = (events, .finished final)) :
    base.run budget state = (events, .finished final) := by
  apply guard_completed_map base blocking id (fun state _ => ?_) budget state final events completed
  simp [Transition.relabel_id]


/-- A covered transition uses the existing machine. A blocked one saves the
whole configuration without evaluating or publishing anything. -/
def machine (dispatch : GroundedDispatch) :
    Machine Configuration ResultPair Configuration ResourceRequest :=
  guardMachine (RecursiveMachine.machine dispatch) (blocked dispatch)

/-- Replenish only the suspended operation. Its caller, earlier results,
remaining alternatives, world and publication history stay retained. -/
def replenish (extra : Nat) (state : Configuration) : Configuration :=
  match state.control, state.stack with
  | .work task, _ => {state with control := .work (task.replenish extra)}
  | .returning _, .fallback value expected bindings depth types :: remaining =>
      {state with stack := .fallback value expected bindings (depth + extra) types :: remaining}
  | _, _ => state

theorem replenish_zero (state : Configuration) : replenish 0 state = state := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task => simp [replenish, Task.replenish_zero]
  | returning results =>
      cases stack with
      | nil => rfl
      | cons frame remaining => cases frame <;> simp [replenish]

theorem replenish_add (first second : Nat) (state : Configuration) :
    replenish second (replenish first state) = replenish (first + second) state := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task => simp [replenish, Task.replenish_add]
  | returning results =>
      cases stack with
      | nil => rfl
      | cons frame remaining => cases frame <;> simp [replenish, Nat.add_assoc]

theorem replenish_space (extra : Nat) (state : Configuration) :
    (replenish extra state).space = state.space := by
  unfold replenish
  split <;> rfl

theorem replenish_emitted (extra : Nat) (state : Configuration) :
    (replenish extra state).emitted = state.emitted := by
  unfold replenish
  split <;> rfl

theorem replenish_work_stack (extra : Nat) (state : Configuration) (task : Task)
    (pending : state.control = .work task) :
    (replenish extra state).stack = state.stack := by simp [replenish, pending]

theorem blocked_run (dispatch : GroundedDispatch) (state : Configuration)
    (request : ResourceRequest) (budget : Nat)
    (pending : blocked dispatch state = some request) :
    (machine dispatch).run (budget + 1) state = ([], .suspended request state) := by
  exact (machine dispatch).run_succ_call (by simp [machine, guardMachine, pending])

/-- Pausing for scheduler budget and continuing from the residual is exact. -/
theorem resume_prefix (dispatch : GroundedDispatch) (state saved : Configuration)
    (first second : Nat) (observed : ResultSet)
    (paused : (machine dispatch).run first state = (observed, .exhausted saved)) :
    (machine dispatch).run (first + second) state =
      (observed ++ ((machine dispatch).run second saved).1,
        ((machine dispatch).run second saved).2) :=
  (machine dispatch).established_and_pending first second state saved observed paused

/-- Continue a pending resource request from its saved configuration after a
depth grant. Scheduler exhaustion resumes with the same evaluator depth.
Binding materialization uses its proved structural depth; the grant applies
to the selected pending evaluation or search operation. -/
def continueRun (dispatch : GroundedDispatch) (budget extra : Nat) :
    ResultSet × Outcome Configuration Configuration ResourceRequest →
      ResultSet × Outcome Configuration Configuration ResourceRequest
  | (events, .suspended _ saved) =>
      let later := (machine dispatch).run budget (replenish extra saved)
      (events ++ later.1, later.2)
  | result => (machine dispatch).continueRun budget result

/-- Completion of the checked machine also completes the original finite
approximation with precisely the same occurrences and retained final state.
The checked machine can additionally suspend, but cannot invent a completion. -/
theorem finished_refines (dispatch : GroundedDispatch) (budget : Nat)
    (state : Configuration) (events : ResultSet) (final : Configuration)
    (completed : (machine dispatch).run budget state = (events, .finished final)) :
    (RecursiveMachine.machine dispatch).run budget state = (events, .finished final) :=
  guard_finished_refines (RecursiveMachine.machine dispatch) (blocked dispatch)
    budget state final events completed

/-! ### Stability after checked completion

Increasing residual evaluator depths commutes with every covered advance.
The proof uses the actual leaf-coverage laws and never infers completeness
from equality of two finite approximations. Publication and saved callers
remain intact. The target is the separately implemented finite evaluator
machine; its logical step count does not include the physical cost of leaves.
-/

def deepenExpansion (extra : Nat) (expanded : Control × List Frame) : Control × List Frame :=
  (expanded.1.deepen extra, expanded.2.map (Frame.deepen extra))

theorem enter_atom_deepen (space : Space) (dispatch : GroundedDispatch)
    (value expected : Atom) (bindings : Bindings) (depth extra : Nat) (live : List Atom) {lookup : TypeLookup}
    (ready : taskReady space dispatch (.atom value expected bindings depth live) lookup = true) :
    enter space dispatch (.atom value expected bindings (depth + extra) live) lookup =
      deepenExpansion extra (enter space dispatch (.atom value expected bindings depth live) lookup) := by
  cases depth with
  | zero => simp [taskReady] at ready
  | succ depth =>
      by_cases empty : isEmptyOrError value = true
      · simp [Nat.succ_add, enter, empty, deepenExpansion, Control.deepen]
      · by_cases trivial : (expected == Atom.atomType || expected == getMetaType value ||
            getMetaType value == Atom.variableType) = true
        · simp [Nat.succ_add, enter, empty, trivial, deepenExpansion, Control.deepen]
        · by_cases scalar : (getMetaType value == Atom.symbolType ||
              getMetaType value == Atom.groundedType || value == Atom.unit) = true
          · have covered : typeCastCovered value expected space bindings depth lookup = true := by
              simpa [taskReady, empty, trivial, scalar] using ready
            simp [Nat.succ_add, enter, empty, trivial, scalar, deepenExpansion, Control.deepen,
              typeCastCovered_stable value expected space bindings depth extra covered]
          · by_cases expression : (getMetaType value == Atom.expressionType) = true
            · simp [Nat.succ_add, enter, empty, trivial, scalar, expression, deepenExpansion, Control.deepen,
                Frame.deepen, Task.replenish]
            · simp [Nat.succ_add, enter, empty, trivial, scalar, expression, deepenExpansion, Control.deepen]

theorem enter_deepen (space : Space) (dispatch : GroundedDispatch)
    (task : Task) (extra : Nat) {lookup : TypeLookup} (ready : taskReady space dispatch task lookup = true) :
    enter space dispatch (task.replenish extra) lookup =
      deepenExpansion extra (enter space dispatch task lookup) := by
  cases task with
  | atom value expected bindings depth live =>
      exact enter_atom_deepen space dispatch value expected bindings depth extra live ready
  | call value expected bindings depth live => rfl
  | invocation mode value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          simp only [taskReady] at ready
          by_cases stopped : mode.errorPassthrough value = true
          · simp only [stopped, ↓reduceIte]
            rfl
          · simp only [stopped, Bool.false_eq_true, ↓reduceIte] at ready ⊢
            split at ready
            · split at ready
              · simp_all only [↓reduceIte]
                repeat' split
                all_goals rfl
              · split at ready
                · simp_all [deepenExpansion, Control.deepen, Task.replenish, Frame.deepen]
                · have stable := queryEquationsCovered_stable _ _ _ depth extra ready
                  simp_all [deepenExpansion, Control.deepen, Task.replenish, Frame.deepen]
            · have stable := queryEquationsCovered_stable _ _ _ depth extra ready
              simp_all [deepenExpansion, Control.deepen, Task.replenish, Frame.deepen]
  | functions value expected bindings depth types live =>
      cases types with
      | nil => rfl
      | cons operatorType remaining =>
          by_cases function : isFunctionType operatorType = true
          · have covered : functionTypeCovered value operatorType expected space bindings depth lookup = true := by
              simpa [taskReady, function] using ready
            have stable := functionTypeCovered_stable value operatorType expected space bindings
              depth extra covered
            simp only [Task.replenish, enter, function, ↓reduceIte, stable]
            cases checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup <;> rfl
          · simp [Task.replenish, enter, function, deepenExpansion, Control.deepen, Frame.deepen]
  | equations original expected incoming depth alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons alternative remaining =>
          rcases alternative with ⟨rhs, selected⟩
          have matching := (Bool.and_eq_true_iff.mp ready).1
          have sameMerge : mergeBindings selected (aliasConstraints incoming) (depth + extra) =
              mergeBindings selected (aliasConstraints incoming) depth := matchCovered_stable depth extra _ matching
          have payload : (mergeBindings selected (aliasConstraints incoming) (depth + extra)).filterMap
                (fun merged => if merged.hasLoop then none else some (merged.applyFull rhs (depth + extra), merged)) =
              (mergeBindings selected (aliasConstraints incoming) depth).filterMap
                (fun merged => if merged.hasLoop then none else some (merged.applyFull rhs depth, merged)) := by
            rw [sameMerge]
            apply List.filterMap_congr
            intro merged member
            have checked := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ready).2 merged member
            by_cases loop : merged.hasLoop = true
            · simp [loop]
            · have covered : merged.applyFullCovered rhs depth = true := by
                simpa [loop] using checked
              rw [merged.applyFullCovered_stable rhs depth extra covered]
          simp only [Task.replenish, enter, payload]
          rfl
  | grounded original expected incoming depth alternatives live =>
      cases alternatives with
      | nil => rfl
      | cons alternative remaining =>
          rcases alternative with ⟨value, selected⟩
          obtain ⟨matching, readings⟩ := Bool.and_eq_true_iff.mp ready
          have same : mergeBindings selected incoming (depth + extra) = mergeBindings selected incoming depth :=
            matchCovered_stable depth extra _ matching
          have payload : (mergeBindings selected incoming (depth + extra)).map
                (fun merged => (merged.applyFull value (depth + extra), merged)) =
              (mergeBindings selected incoming depth).map
                (fun merged => (merged.applyFull value depth, merged)) := by
            rw [same]
            apply List.map_congr_left
            intro merged member
            rw [merged.applyFullCovered_stable value depth extra
              (List.all_eq_true.mp readings merged member)]
          simp only [Task.replenish, enter, payload]
          rfl
  | expression value expected bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          repeat' split
          all_goals simp [deepenExpansion, Control.deepen, Frame.deepen, Task.replenish]
  | func value operatorType bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> rfl
  | args values types bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> rfl
  | tuple value bindings depth live =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> rfl
  | heads operatorType arguments depth alternatives live =>
      cases alternatives <;> simp only [Task.replenish, enter]
      · rfl
      · repeat' split
        all_goals rfl
  | argumentHeads original remaining types depth alternatives live =>
      cases alternatives <;> simp only [Task.replenish, enter]
      · rfl
      · split <;> rfl
  | tupleHeads tail depth alternatives live =>
      cases alternatives <;> simp only [Task.replenish, enter]
      · rfl
      · split <;> rfl
  | bindingAlternatives value operatorType expected depth alternatives live =>
      cases alternatives <;> rfl
  | calls expected depth alternatives live => cases alternatives <;> rfl
  | atoms expected depth alternatives live => cases alternatives <;> rfl
  | returned original value expected bindings depth live =>
      simp only [Task.replenish, enter]
      split <;> try rfl
      split <;> rfl
  | returns original expected depth alternatives live => cases alternatives <;> rfl
  | tupleCalls value expected bindings depth live => rfl
  | produced value bindings depth live caller provenance =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          repeat' split
          all_goals rfl
  | productions depth alternatives live caller provenance => cases alternatives <;> rfl
  | minimal value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          repeat' split
          all_goals rfl
  | minimals depth alternatives live caller => cases alternatives <;> rfl
  | primitive value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          split <;> try rfl
          · rename_i atom
            have checked : bindings.applyFullCovered atom depth = true := by
              simpa [taskReady, minimalCoreSupported] using ready
            rw [bindings.applyFullCovered_stable atom depth extra checked]
            rfl
          · rename_i target pattern yes no
            have checked : unifyMatchesCovered target pattern bindings depth = true := by
              simpa [taskReady, minimalCoreSupported] using ready
            have stable := unifyMatchesCovered_stable target pattern yes bindings depth extra checked
            rw [stable]
            rfl
  | chainRows name template depth alternatives =>
      cases alternatives with
      | nil => rfl
      | cons pair remaining =>
          rcases pair with ⟨value, bindings⟩
          have same := bindings.applyFullCovered_stable value depth extra ready
          simp only [Task.replenish, enter, same]
          rfl
  | functionBody value bindings depth live caller =>
      cases depth with
      | zero => simp [taskReady] at ready
      | succ depth =>
          simp only [Task.replenish, Nat.succ_add, enter]
          rfl
  | bodyResults depth alternatives live caller =>
      cases alternatives with
      | nil => rfl
      | cons pair remaining =>
          rcases pair with ⟨value, bindings⟩
          have same := bindings.applyFullCovered_stable value depth extra ready
          simp only [Task.replenish, enter, same]
          split <;> rfl
  | producerResults mode original incoming fuel live emptyReply results =>
      cases results <;> rfl
  | completed value expected bindings depth =>
      simp only [taskReady] at ready
      simp only [Task.replenish, enter, completedCallReturn]
      split at ready
      · simp_all [deepenExpansion, Control.deepen]
      · have stable := typeCastCovered_stable value expected space bindings depth extra ready
        simp_all [deepenExpansion, Control.deepen]

theorem functionFallback_deepen (space : Space) (value expected : Atom) (bindings : Bindings)
    (depth extra : Nat) (types : List Atom) (results : ResultSet) {lookup : TypeLookup}
    (ready : frameReady space results (.fallback value expected bindings depth types) lookup = true) :
    functionFallback space value expected bindings (depth + extra) types results lookup =
      functionFallback space value expected bindings depth types results lookup := by
  by_cases nonempty : results.isEmpty = false
  · simp [functionFallback, nonempty]
  · have coveredTypes : (types.all fun operatorType => !isFunctionType operatorType ||
          functionTypeCovered value operatorType expected space bindings depth lookup) = true := by
      have empty : results.isEmpty = true := by cases found : results.isEmpty <;> simp_all
      simpa [frameReady, empty] using ready
    have stable (operatorType : Atom) (member : operatorType ∈ types)
        (function : isFunctionType operatorType = true) :
        checkIfFunctionTypeIsApplicable value operatorType expected space bindings (depth + extra) lookup =
          checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup := by
      apply functionTypeCovered_stable
      simpa [function] using List.all_eq_true.mp coveredTypes operatorType member
    have tests :
        types.map (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings (depth + extra) lookup with
          | .inl _ => true
          | .inr _ => false
        else true) =
        types.map (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup with
          | .inl _ => true
          | .inr _ => false
        else true) := by
      apply List.map_congr_left
      intro operatorType member
      by_cases function : isFunctionType operatorType = true
      · rw [if_pos function, if_pos function, stable operatorType member function]
      · rw [if_neg function, if_neg function]
    have checks := congrArg (fun answers : List Bool => answers.all id) tests
    simp only [List.all_map, Function.comp_def, id_eq] at checks
    have blocks : types.flatMap (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings (depth + extra) lookup with
          | .inl errors => errors.map fun error => (error, bindings)
          | .inr _ => []
        else []) =
        types.flatMap (fun operatorType => if isFunctionType operatorType then
          match checkIfFunctionTypeIsApplicable value operatorType expected space bindings depth lookup with
          | .inl errors => errors.map fun error => (error, bindings)
          | .inr _ => []
        else []) := by
      apply List.flatMap_congr
      intro operatorType member
      by_cases function : isFunctionType operatorType = true
      · rw [if_pos function, if_pos function, stable operatorType member function]
      · rw [if_neg function, if_neg function]
    dsimp only [functionFallback]
    congr 1
    congr 1
    congr 1

theorem resume_deepen (space : Space) (frame : Frame) (results : ResultSet)
    (extra : Nat) {lookup : TypeLookup} (ready : frameReady space results frame lookup = true) :
    resume space (frame.deepen extra) results lookup = deepenExpansion extra (resume space frame results lookup) := by
  cases frame with
  | fallback value expected bindings depth types =>
      simp only [Frame.deepen, resume, deepenExpansion, Control.deepen, List.map_nil]
      rw [functionFallback_deepen space value expected bindings depth extra types results ready]
  | invocationReturn mode original fuel live => cases mode <;> rfl
  | producerResults mode original incoming fuel live emptyReply =>
      cases results <;> rfl
  | _ => rfl

theorem step_deepen (dispatch : GroundedDispatch) (state : Configuration) (extra : Nat)
    (ready : blocked dispatch state = none) :
    (RecursiveMachine.machine dispatch).step (state.deepen extra) =
      ((RecursiveMachine.machine dispatch).step state).map (fun transition =>
        (transition.mapState (Configuration.deepen extra)).relabel id (Configuration.deepen extra) id) := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task =>
      have covered : taskReady space dispatch task = true := by
        simpa [blocked] using ready
      have commute := enter_deepen space dispatch task extra covered
      simp only [RecursiveMachine.machine, next, Configuration.deepen, Control.deepen, commute,
        deepenExpansion, List.map_append, Option.map_some, Transition.mapState, Transition.relabel]
  | returning results =>
      cases stack with
      | nil => cases results <;> rfl
      | cons frame remaining =>
          have covered : frameReady space results frame = true := by
            simpa [blocked] using ready
          have commute := resume_deepen space frame results extra covered
          simp only [RecursiveMachine.machine, next, Configuration.deepen, Control.deepen,
            List.map_cons, commute, deepenExpansion, List.map_append,
            Option.map_some, Transition.mapState, Transition.relabel]

/-- A completed checked run earns the same result at every greater residual
depth. The statement follows arbitrary actual configurations, not only fresh
top-level requests, and keeps the complete final continuation. -/
theorem completed_deepen (dispatch : GroundedDispatch) (extra budget : Nat)
    (state final : Configuration) (events : ResultSet)
    (completed : (machine dispatch).run budget state = (events, .finished final)) :
    (RecursiveMachine.machine dispatch).run budget (state.deepen extra) =
      (events, .finished (final.deepen extra)) :=
  guard_completed_map (RecursiveMachine.machine dispatch) (blocked dispatch)
    (Configuration.deepen extra) (fun state ready => step_deepen dispatch state extra ready)
    budget state final events completed

end Checked

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine

namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Type Spec.Eval.Steps
open Spec.Eval.Completed (Policy Result WorldServices)
open RecursiveTasks.Contextual
open Mettapedia.Machines.OrderedProtocol.Completion

/-! ## Small steps of contextual completed-phase control

Casting, complete static signature selection, equation queries and contextual
unification are primitive premises. Every recursive language evaluation becomes pending work
with an explicit continuation. A returned batch is published only after its
surrounding phase has finished. The relation retains source freshening choices;
selecting a concrete fresh-name/query implementation is a later realization.
-/

inductive LocalStepWith (admission : Completed.ArgumentService) : Space → Spec.Eval.GroundedDispatch → Completed.CastLookup → Policy →
    Control × List Continuation → Control × List Continuation → Prop where
  | delivered {space dispatch lookup policy live scope value expected activation stack} :
      Entry.Rel policy.reentry (activation.read policy value).status
        (activation.read policy value).erase expected .deliver →
      LocalStepWith admission space dispatch lookup policy
        (.work (.atom live scope value expected activation),stack)
        (.returning [(activation.read policy value,activation)],stack)
  | cast {space dispatch lookup policy live scope value expected activation raw results stack} :
      Entry.Rel policy.reentry (activation.read policy value).status
        (activation.read policy value).erase expected .cast →
      TypeCastBatchRel space (activation.read policy value).erase expected activation.bindings raw
        (lookup := lookup (invocationTypeScope scope live
          (activation.read policy value).erase expected activation.bindings) space)
        (matching := policy.matching.Rel) →
      List.Forall₂ (Completed.CastResultRel policy
        (lookup (invocationTypeScope scope live
          (activation.read policy value).erase expected activation.bindings) space)
        activation (activation.read policy value) expected) raw results →
      LocalStepWith admission space dispatch lookup policy
        (.work (.atom live scope value expected activation),stack) (.returning results,stack)
  | atomTuple {space dispatch lookup policy live scope value expected activation readiness operator arguments stack} :
      Entry.Rel policy.reentry (activation.read policy value).status
        (activation.read policy value).erase expected .interpret →
      activation.read policy value = .expression readiness (operator :: arguments) →
      TypeOccurrencesRel (space.atoms : Multiset Atom) operator.erase {Atom.undefinedType} →
      LocalStepWith admission space dispatch lookup policy
        (.work (.atom live scope value expected activation),stack)
        (.work (.tuple (expected :: live) scope (operator :: arguments) activation),
          .calls live scope expected :: .publish (activation.read policy value).erase :: stack)
  | atomFunction {space dispatch lookup policy live scope value expected activation readiness operator arguments signature frames stack} :
      Entry.Rel policy.reentry (activation.read policy value).status
        (activation.read policy value).erase expected .interpret →
      activation.read policy value = .expression readiness (operator :: arguments) →
      admission.selection space lookup policy live scope (activation.read policy value).erase
        operator.erase expected activation (.selected signature frames) →
      LocalStepWith admission space dispatch lookup policy
        (.work (.atom live scope value expected activation),stack)
        (.work (.invocations live scope expected signature operator arguments frames),
          .publish (activation.read policy value).erase :: stack)
  | atomFallback {space dispatch lookup policy live scope value expected activation readiness operator arguments errors stack} :
      Entry.Rel policy.reentry (activation.read policy value).status
        (activation.read policy value).erase expected .interpret →
      activation.read policy value = .expression readiness (operator :: arguments) →
      admission.selection space lookup policy live scope (activation.read policy value).erase
        operator.erase expected activation (.exhausted errors true) →
      LocalStepWith admission space dispatch lookup policy
        (.work (.atom live scope value expected activation),stack)
        (.work (.tuple (expected :: live) scope (operator :: arguments) activation),
          .calls live scope expected :: .diagnostics errors activation ::
            .publish (activation.read policy value).erase :: stack)
  | atomSelectionFailed {space dispatch lookup policy live scope value expected activation readiness operator arguments errors stack} :
      Entry.Rel policy.reentry (activation.read policy value).status
        (activation.read policy value).erase expected .interpret →
      activation.read policy value = .expression readiness (operator :: arguments) →
      admission.selection space lookup policy live scope (activation.read policy value).erase
        operator.erase expected activation (.exhausted errors false) →
      LocalStepWith admission space dispatch lookup policy
        (.work (.atom live scope value expected activation),stack)
        (.returning (Completed.diagnosticResults errors activation),
          .publish (activation.read policy value).erase :: stack)
  | tupleNil {space dispatch lookup policy live scope activation stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.tuple live scope [] activation),stack)
        (.returning [(.expression .active [],activation)],stack)
  | tupleSingleton {space dispatch lookup policy live scope value activation stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.tuple live scope [value] activation),stack)
        (.work (.atom live scope value Atom.undefinedType activation),.singleton :: stack)
  | tupleCons {space dispatch lookup policy live scope head second remaining activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.tuple live scope (head :: second :: remaining) activation),stack)
        (.work (.atom (.expression ((second :: remaining).map Entry.Value.erase) :: live)
          scope head Atom.undefinedType activation),.branches live scope (second :: remaining) :: stack)
  | branchesNil {space dispatch lookup policy live scope tail stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.branches live scope tail []),stack) (.returning [],stack)
  | branchesStopped {space dispatch lookup policy live scope tail head heads stack} :
      IsEmptyOrErrorRel head.1.erase →
      LocalStepWith admission space dispatch lookup policy (.work (.branches live scope tail (head :: heads)),stack)
        (.work (.branches live scope tail heads),.prepend [head] :: stack)
  | branchesContinue {space dispatch lookup policy live scope tail head heads stack} :
      ¬IsEmptyOrErrorRel head.1.erase →
      LocalStepWith admission space dispatch lookup policy (.work (.branches live scope tail (head :: heads)),stack)
        (.work (.tuple (head.1.erase :: live) scope tail head.2),
          .tupleTail head.1 :: .append (.branches live scope tail heads) :: stack)
  | argumentsNil {space dispatch lookup policy live scope activation stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.arguments live scope [] activation),stack)
        (.returning [(Entry.Value.argumentPacket [],activation)],stack)
  | argumentsCons {space dispatch lookup policy live scope request requests activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.arguments live scope (request :: requests) activation),stack)
        (.work (.atom (Completed.argumentScope requests ++ live) scope request.1 request.2 activation),
          .arguments live scope request.1 requests :: stack)
  | argumentBranchesNil {space dispatch lookup policy live scope original requests stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.argumentBranches live scope original requests []),stack) (.returning [],stack)
  | argumentBranchesStopped {space dispatch lookup policy live scope original requests head heads stack} :
      Completed.ArgumentStopped original head →
      LocalStepWith admission space dispatch lookup policy
        (.work (.argumentBranches live scope original requests (head :: heads)),stack)
        (.work (.argumentBranches live scope original requests heads),.prepend [head] :: stack)
  | argumentBranchesContinue {space dispatch lookup policy live scope original requests head heads stack} :
      ¬Completed.ArgumentStopped original head →
      LocalStepWith admission space dispatch lookup policy
        (.work (.argumentBranches live scope original requests (head :: heads)),stack)
        (.work (.arguments (head.1.erase :: live) scope requests head.2),
          .argumentTail head.1 :: .append (.argumentBranches live scope original requests heads) :: stack)
  | functionStart {space dispatch lookup policy live scope expected signature operator arguments activation stack} :
      arguments.length = signature.argumentTypes.length →
      LocalStepWith admission space dispatch lookup policy
        (.work (.function live scope expected signature operator arguments activation),stack)
        (.work (.atom (signature.functionType :: arguments.map Entry.Value.erase ++ live)
          (scope ++ expectedApplicationScope (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
          operator signature.functionType activation),
          .functionHeads live scope (arguments.zip signature.argumentTypes) :: stack)
  | functionBranchesNil {space dispatch lookup policy live scope requests stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.functionBranches live scope requests []),stack) (.returning [],stack)
  | functionBranchesStopped {space dispatch lookup policy live scope requests head heads stack} :
      IsEmptyOrErrorRel head.1.erase →
      LocalStepWith admission space dispatch lookup policy
        (.work (.functionBranches live scope requests (head :: heads)),stack)
        (.work (.functionBranches live scope requests heads),.prepend [head] :: stack)
  | functionBranchesContinue {space dispatch lookup policy live scope requests head heads stack} :
      ¬IsEmptyOrErrorRel head.1.erase →
      LocalStepWith admission space dispatch lookup policy
        (.work (.functionBranches live scope requests (head :: heads)),stack)
        (.work (.arguments (head.1.erase :: live) scope requests head.2),
          .functionAssemble head.1 :: .append (.functionBranches live scope requests heads) :: stack)
  | invocationsNil {space dispatch lookup policy live scope expected signature operator arguments stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.invocations live scope expected signature operator arguments []),stack) (.returning [],stack)
  | invocationsCons {space dispatch lookup policy live scope expected signature operator arguments activation activations stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.invocations live scope expected signature operator arguments (activation :: activations)),stack)
        (.work (.function (Completed.invocationReturnType signature :: live) scope expected signature
          operator arguments activation),
          .calls live scope (Completed.invocationReturnType signature) ::
            .append (.invocations live scope expected signature operator arguments activations) :: stack)
  | callsNil {space dispatch lookup policy live scope expected stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.calls live scope expected []),stack) (.returning [],stack)
  | callsCons {space dispatch lookup policy live scope expected head heads stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.calls live scope expected (head :: heads)),stack)
        (.work (.call live scope head.1 expected head.2),.append (.calls live scope expected heads) :: stack)
  | callError {space dispatch lookup policy live scope value expected activation stack} :
      IsErrorRel value.erase →
      LocalStepWith admission space dispatch lookup policy (.work (.call live scope value expected activation),stack)
        (.returning [(value,activation)],stack)
  | callEmbedded {space dispatch lookup policy live scope value expected activation stack} :
      ¬IsErrorRel value.erase → ¬Minimal.HostCall dispatch value.erase →
      Minimal.embeddedInstruction value.erase = true →
      LocalStepWith admission space dispatch lookup policy (.work (.call live scope value expected activation),stack)
        (.work (.invocation (expected :: live) scope none value activation),
          .boundaryBatch live scope none (.returned value expected) :: stack)
  | callAbsent {space dispatch lookup policy live scope value expected activation stack} :
      ¬IsErrorRel value.erase → NonGroundedCallRel dispatch value.erase →
      EquationFrontierRel space (expected :: live) value.erase activation.bindings [] →
      LocalStepWith admission space dispatch lookup policy (.work (.call live scope value expected activation),stack)
        (.returning [(value,activation)],stack)
  | callEquations {space dispatch lookup policy live scope value expected activation works stack} :
      ¬IsErrorRel value.erase → NonGroundedCallRel dispatch value.erase →
      EquationFrontierRel space (expected :: live) value.erase activation.bindings works → works ≠ [] →
      LocalStepWith admission space dispatch lookup policy (.work (.call live scope value expected activation),stack)
        (.work (.equations live scope value expected activation works),stack)
  | equationsNil {space dispatch lookup policy live scope original expected activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.equations live scope original expected activation []),stack) (.returning [],stack)
  | equationsCons {space dispatch lookup policy live scope original expected activation work works output stack} :
      output.bindings = work.bindings →
      Entry.Value.UnifyRel policy.rebuilding activation.environment original (Entry.Value.ofAtom work.pattern)
        output.environment →
      LocalStepWith admission space dispatch lookup policy
        (.work (.equations live scope original expected activation (work :: works)),stack)
        (.work (.boundary (expected :: live) scope (some original.erase) .producer
          (output.read policy (Entry.Value.ofAtom work.body)) output),
          .boundaryBatch live scope none (.returned original expected) ::
          .append (.equations live scope original expected activation works) :: stack)
  | returnRefused {space dispatch lookup policy live scope original expected value activation stack} :
      value.erase = Atom.notReducible →
      LocalStepWith admission space dispatch lookup policy
        (.work (.returned live scope original expected value activation),stack)
        (.returning [(original,activation)],stack)
  | returnStopped {space dispatch lookup policy live scope original expected value activation stack} :
      IsEmptyOrErrorRel value.erase →
      LocalStepWith admission space dispatch lookup policy
        (.work (.returned live scope original expected value activation),stack)
        (.returning [(value,activation)],stack)
  | returnEvaluate {space dispatch lookup policy live scope original expected value activation stack} :
      value.erase ≠ Atom.notReducible → ¬IsEmptyOrErrorRel value.erase →
      LocalStepWith admission space dispatch lookup policy
        (.work (.returned live scope original expected value activation),stack)
        (.work (.atom live scope value expected activation),stack)
  | minimalData {space dispatch lookup policy live scope caller value activation stack} :
      Minimal.embeddedInstruction value.erase = false →
      LocalStepWith admission space dispatch lookup policy (.work (.minimal live scope caller value activation),stack)
        (.returning [(value,activation)],stack)
  | minimalEval {space dispatch lookup policy live scope caller readiness operand activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller (.expression readiness [.symbol "eval",operand]) activation),stack)
        (.work (.invocation live scope caller (activation.read policy operand) activation),stack)
  | minimalEvalc {space context dispatch lookup policy live scope caller readiness operand activation services enumeration stack} :
      dispatch.minimal = some ⟨services,enumeration⟩ →
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller
          (.expression readiness [.symbol "evalc",operand,.grounded (services.contextPayload context)]) activation),stack)
        (.context context (.work (.invocation live scope caller (activation.read policy operand) activation)) [],stack)
  | minimalChain {space dispatch lookup policy live scope caller readiness operand name template activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller (.expression readiness [.symbol "chain",operand,.var name,template]) activation),stack)
        (.work (.minimal ((.expression [.symbol "chain",operand.erase,.var name,template.erase]) :: live) scope
          (some (.expression [.symbol "chain",operand.erase,.var name,template.erase])) operand activation),
          .boundaryBatch live scope caller (.chain name template) :: stack)
  | minimalUnifyYes {space dispatch lookup policy live scope caller readiness target pattern yes no activation output stack} :
      UnifyCandidateRel target.erase pattern.erase activation.bindings output.bindings →
      Entry.Value.UnifyRel policy.rebuilding activation.environment target pattern output.environment →
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller (.expression readiness [.symbol "unify",target,pattern,yes,no]) activation),stack)
        (.returning [(output.read policy yes,output)],stack)
  | minimalUnifyNo {space dispatch lookup policy live scope caller readiness target pattern yes no activation stack} :
      UnifyNoMatchRel target.erase pattern.erase activation.bindings →
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller (.expression readiness [.symbol "unify",target,pattern,yes,no]) activation),stack)
        (.returning [(no,activation)],stack)
  | minimalUnifyBadArity {space dispatch lookup policy live scope caller readiness tail activation stack} :
      tail.length ≠ 4 →
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller (.expression readiness (.symbol "unify" :: tail)) activation),stack)
        (.returning [(Entry.Value.ofAtom (mkErrorMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase))
          (dispatch.unifyBadArityMessage (.expression (.symbol "unify" :: tail.map Entry.Value.erase)))),activation)],stack)
  | minimalConsAtom {space dispatch lookup policy live scope caller readiness tailReadiness head tail activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller
          (.expression readiness [.symbol "cons-atom",head,.expression tailReadiness tail]) activation),stack)
        (.returning [(.expression .active (head :: tail),activation)],stack)
  | minimalDeconsAtom {space dispatch lookup policy live scope caller readiness valueReadiness head tail activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller
          (.expression readiness [.symbol "decons-atom",.expression valueReadiness (head :: tail)]) activation),stack)
        (.returning [(.expression .active [head,.expression .active tail],activation)],stack)
  | minimalFunction {space dispatch lookup policy live scope caller readiness body bodyReadiness children activation stack} :
      body = .expression bodyReadiness children →
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller (.expression readiness [.symbol "function",body]) activation),stack)
        (.work (.body ((.expression [.symbol "function",body.erase]) :: live) scope
          (some (.expression [.symbol "function",body.erase])) body activation),
          .boundaryBatch live scope caller .functionDone :: stack)
  | minimalMetta {space context dispatch lookup policy live scope caller readiness operand expected activation services enumeration stack} :
      dispatch.minimal = some ⟨services,enumeration⟩ →
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller
          (.expression readiness [.symbol "metta",operand,expected,.grounded (services.contextPayload context)]) activation),stack)
        (.context context (.work (.atom live scope operand expected.erase activation)) [],stack)
  | minimalContextSpace {space dispatch lookup policy live scope caller readiness activation services enumeration stack} :
      dispatch.minimal = some ⟨services,enumeration⟩ →
      LocalStepWith admission space dispatch lookup policy
        (.work (.minimal live scope caller (.expression readiness [.symbol "context-space"]) activation),stack)
        (.returning [(.grounded (services.contextPayload space),activation)],stack)
  | bodyStart {space dispatch lookup policy live scope caller value activation stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.body live scope caller value activation),stack)
        (.work (.minimal live scope caller value activation),.boundaryBatch live scope caller .body :: stack)
  | invocationEmbedded {space dispatch lookup policy live scope caller value activation stack} :
      ¬Minimal.HostCall dispatch value.erase → Minimal.embeddedInstruction value.erase = true →
      LocalStepWith admission space dispatch lookup policy (.work (.invocation live scope caller value activation),stack)
        (.work (.minimal live scope caller value activation),stack)
  | invocationAbsent {space dispatch lookup policy live scope caller value activation stack} :
      NonGroundedCallRel dispatch value.erase → EquationFrontierRel space live value.erase activation.bindings [] →
      LocalStepWith admission space dispatch lookup policy (.work (.invocation live scope caller value activation),stack)
        (.returning [(.symbol "NotReducible",activation)],stack)
  | invocationEquations {space dispatch lookup policy live scope caller value activation works stack} :
      NonGroundedCallRel dispatch value.erase →
      EquationFrontierRel space live value.erase activation.bindings works → works ≠ [] →
      LocalStepWith admission space dispatch lookup policy (.work (.invocation live scope caller value activation),stack)
        (.work (.invocationEquations live scope value activation works),stack)
  | invocationEquationsNil {space dispatch lookup policy live scope original activation stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.invocationEquations live scope original activation []),stack) (.returning [],stack)
  | invocationEquationsCons {space dispatch lookup policy live scope original activation work works output stack} :
      output.bindings = work.bindings →
      Entry.Value.UnifyRel policy.rebuilding activation.environment original (Entry.Value.ofAtom work.pattern) output.environment →
      LocalStepWith admission space dispatch lookup policy (.work (.invocationEquations live scope original activation (work :: works)),stack)
        (.work (.boundary live scope (some original.erase) .producer (output.read policy (Entry.Value.ofAtom work.body)) output),
          .append (.invocationEquations live scope original activation works) :: stack)
  | boundaryChain {space dispatch lookup policy live scope caller name template value activation stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.boundary live scope caller (.chain name template) value activation),stack)
        (.work (.minimal live scope caller (Completed.substituteBinder policy name (activation.read policy value) template) activation),stack)
  | boundaryBodyTerminal {space dispatch lookup policy live scope caller value activation stack} :
      Minimal.embeddedInstruction (activation.read policy value).erase = false →
      LocalStepWith admission space dispatch lookup policy (.work (.boundary live scope caller .body value activation),stack)
        (.returning [(activation.read policy value,activation)],stack)
  | boundaryBodyResume {space dispatch lookup policy live scope caller value activation stack} :
      Minimal.embeddedInstruction (activation.read policy value).erase = true →
      LocalStepWith admission space dispatch lookup policy (.work (.boundary live scope caller .body value activation),stack)
        (.work (.body live scope caller (activation.read policy value) activation),stack)
  | boundaryFunctionReturn {space dispatch lookup policy live scope caller readiness returned activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.boundary live scope caller .functionDone (.expression readiness [.symbol "return",returned]) activation),stack)
        (.returning [(returned,activation)],stack)
  | boundaryFunctionNoReturn {space dispatch lookup policy live scope caller value activation stack} :
      (∀ returned, value.erase ≠ .expression [.symbol "return",returned]) →
      LocalStepWith admission space dispatch lookup policy (.work (.boundary live scope caller .functionDone value activation),stack)
        (.returning [(Entry.Value.ofAtom (Minimal.functionTerminalResult caller value.erase),activation)],stack)
  | boundaryProducerRaw {space dispatch lookup policy live scope caller value activation stack} :
      ¬Completed.FunctionPending policy value →
      LocalStepWith admission space dispatch lookup policy (.work (.boundary live scope caller .producer value activation),stack)
        (.returning [(value,activation)],stack)
  | boundaryProducerFunction {space dispatch lookup policy live scope caller value activation stack} :
      Completed.FunctionPending policy value →
      LocalStepWith admission space dispatch lookup policy (.work (.boundary live scope caller .producer value activation),stack)
        (.work (.minimal live scope caller value activation),stack)
  | boundaryReturned {space dispatch lookup policy live scope caller original expected value activation stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.boundary live scope caller (.returned original expected) value activation),stack)
        (.work (.returned live scope original expected value activation),stack)
  | boundaryBatchNil {space dispatch lookup policy live scope caller site stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.boundaryBatch live scope caller site []),stack) (.returning [],stack)
  | boundaryBatchCons {space dispatch lookup policy live scope caller site head heads stack} :
      LocalStepWith admission space dispatch lookup policy (.work (.boundaryBatch live scope caller site (head :: heads)),stack)
        (.work (.boundary live scope caller site head.1 head.2),.append (.boundaryBatch live scope caller site heads) :: stack)
  | boundaryNativeEmittedRaw {space dispatch lookup policy live scope caller original value activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.boundary live scope caller (.native original none .emitted) value activation),stack)
        (.work (.boundary live scope (some original.erase) .producer value activation),stack)
  | boundaryNativeEmittedReturn {space dispatch lookup policy live scope caller original expected value activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.boundary live scope caller (.native original (some expected) .emitted) value activation),stack)
        (.work (.boundary (expected :: live) scope (some original.erase) .producer value activation),
          .boundaryBatch live scope caller (.returned original expected) :: stack)
  | boundaryNativeCompletedRaw {space dispatch lookup policy live scope caller original value activation stack} :
      LocalStepWith admission space dispatch lookup policy
        (.work (.boundary live scope caller (.native original none .completed) value activation),stack)
        (.returning [(value,activation)],stack)
  | boundaryNativeCompletedReturn {space dispatch lookup policy live scope caller original expected value activation results stack} :
      Completed.NativeCompletedReturnRel space
        (lookup (invocationTypeScope scope live original.erase expected activation.bindings) space)
        policy value expected activation results →
      LocalStepWith admission space dispatch lookup policy
        (.work (.boundary live scope caller (.native original (some expected) .completed) value activation),stack)
        (.returning results,stack)
  | publish {space dispatch lookup policy original raw selected stack} :
      SuccessPriorityRel (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Completed.readResult policy)) selected →
      LocalStepWith admission space dispatch lookup policy (.returning raw,.publish original :: stack)
        (.returning (selected.map (Completed.publishResult policy original)),stack)
  | singleton {space dispatch lookup policy results stack} :
      LocalStepWith admission space dispatch lookup policy (.returning results,.singleton :: stack)
        (.returning (results.map Completed.tupleSingleton),stack)
  | branches {space dispatch lookup policy live scope tail heads stack} :
      LocalStepWith admission space dispatch lookup policy (.returning heads,.branches live scope tail :: stack)
        (.work (.branches live scope tail heads),stack)
  | tupleTail {space dispatch lookup policy head results stack} :
      LocalStepWith admission space dispatch lookup policy (.returning results,.tupleTail head :: stack)
        (.returning (results.map (Completed.tuplePrepend head)),stack)
  | arguments {space dispatch lookup policy live scope original requests heads stack} :
      LocalStepWith admission space dispatch lookup policy (.returning heads,.arguments live scope original requests :: stack)
        (.work (.argumentBranches live scope original requests heads),stack)
  | argumentTail {space dispatch lookup policy head results stack} :
      LocalStepWith admission space dispatch lookup policy (.returning results,.argumentTail head :: stack)
        (.returning (results.map (Completed.argumentPrepend head)),stack)
  | functionHeads {space dispatch lookup policy live scope requests heads stack} :
      LocalStepWith admission space dispatch lookup policy (.returning heads,.functionHeads live scope requests :: stack)
        (.work (.functionBranches live scope requests heads),stack)
  | functionAssemble {space dispatch lookup policy head results stack} :
      LocalStepWith admission space dispatch lookup policy (.returning results,.functionAssemble head :: stack)
        (.returning (results.map (Completed.functionAssemble head)),stack)
  | diagnostics {space dispatch lookup policy errors activation results stack} :
      LocalStepWith admission space dispatch lookup policy (.returning results,.diagnostics errors activation :: stack)
        (.returning (results ++ Completed.diagnosticResults errors activation),stack)
  | boundaryBatch {space dispatch lookup policy live scope caller site rows stack} :
      LocalStepWith admission space dispatch lookup policy (.returning rows,.boundaryBatch live scope caller site :: stack)
        (.work (.boundaryBatch live scope caller site rows),stack)
  | calls {space dispatch lookup policy live scope expected rows stack} :
      LocalStepWith admission space dispatch lookup policy (.returning rows,.calls live scope expected :: stack)
        (.work (.calls live scope expected rows),stack)
  | append {space dispatch lookup policy remaining results stack} :
      LocalStepWith admission space dispatch lookup policy (.returning results,.append remaining :: stack)
        (.work remaining,.prepend results :: stack)
  | prepend {space dispatch lookup policy selected results stack} :
      LocalStepWith admission space dispatch lookup policy (.returning results,.prepend selected :: stack)
        (.returning (selected ++ results),stack)
  | contextStep {space context dispatch lookup policy child inner next remaining stack} :
      LocalStepWith admission context dispatch lookup policy (child,inner) (next,remaining) →
      LocalStepWith admission space dispatch lookup policy (.context context child inner,stack)
        (.context context next remaining,stack)
  | contextReturn {space context dispatch lookup policy results stack} :
      LocalStepWith admission space dispatch lookup policy (.context context (.returning results) [],stack)
        (.returning results,stack)

/-- The existing interface selects historical argument queries unless a
separate operand-admission service is explicitly supplied. -/
abbrev LocalStep (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy)
    (before after : Control × List Continuation)
    (admission : Completed.ArgumentService := .historical) : Prop :=
  LocalStepWith admission space dispatch lookup policy before after

namespace LocalStep
export LocalStepWith (
  delivered cast atomTuple atomFunction atomFallback atomSelectionFailed tupleNil tupleSingleton tupleCons branchesNil branchesStopped branchesContinue argumentsNil argumentsCons argumentBranchesNil argumentBranchesStopped argumentBranchesContinue functionStart functionBranchesNil functionBranchesStopped functionBranchesContinue invocationsNil invocationsCons callsNil callsCons callError callEmbedded callAbsent callEquations equationsNil equationsCons returnRefused returnStopped returnEvaluate minimalData minimalEval minimalEvalc minimalChain minimalUnifyYes minimalUnifyNo minimalUnifyBadArity minimalConsAtom minimalDeconsAtom minimalFunction minimalMetta minimalContextSpace bodyStart invocationEmbedded invocationAbsent invocationEquations invocationEquationsNil invocationEquationsCons boundaryChain boundaryBodyTerminal boundaryBodyResume boundaryFunctionReturn boundaryFunctionNoReturn boundaryProducerRaw boundaryProducerFunction boundaryReturned boundaryBatchNil boundaryBatchCons boundaryNativeEmittedRaw boundaryNativeEmittedReturn boundaryNativeCompletedRaw boundaryNativeCompletedReturn publish singleton branches tupleTail arguments argumentTail functionHeads functionAssemble diagnostics boundaryBatch calls append prepend contextStep contextReturn
)
end LocalStep

inductive Step (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) : Configuration → Configuration → Prop where
  | internal {space before stack after remaining emitted} :
      LocalStep space dispatch lookup policy (before,stack) (after,remaining) →
      Step dispatch lookup policy ⟨space,before,stack,emitted⟩ ⟨space,after,remaining,emitted⟩
  | publish {space head tail emitted} :
      Step dispatch lookup policy ⟨space,.returning (head :: tail),[],emitted⟩
        ⟨space,.returning tail,[],emitted ++ [head]⟩

abbrev LocalSteps (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) :=
  Relation.ReflTransGen (LocalStep space dispatch lookup policy)

abbrev Steps (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup)
    (policy : Policy) := Relation.ReflTransGen (Step dispatch lookup policy)

/-- Load source syntax as fresh work with an empty logical activation. -/
def load (space : Space) (value expected : Atom) : Configuration :=
  Configuration.initial space (.atom [] [] (Entry.Value.ofAtom value) expected Completed.Frame.empty)

/-- Observe a completed phase only after its continuation and publication
queue are exhausted. Pending work is not an empty answer batch. -/
def observe (state : Configuration) : Option (List Result) :=
  match state.control,state.stack with
  | .returning [],[] => some state.emitted
  | _,_ => none

theorem observe_eq_some {state : Configuration} {answers : List Result}
    (observed : observe state = some answers) :
    state = ⟨state.space,.returning [],[],answers⟩ := by
  cases state with
  | mk space control stack emitted =>
      cases control with
      | work => simp [observe] at observed
      | context => simp [observe] at observed
      | returning results =>
          cases results <;> cases stack <;> simp_all [observe]

theorem observed_final {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Policy} {state : Configuration} {answers : List Result}
    (observed : observe state = some answers) :
    ¬∃ after, Step dispatch lookup policy state after := by
  have same := observe_eq_some observed
  rw [same]
  rintro ⟨after,advanced⟩
  cases advanced with
  | internal advance => cases advance

/-- The common reduction-span interface retains the actual machine edges.
Answer occurrences remain in the ordered publication history. -/
def span (dispatch : Spec.Eval.GroundedDispatch) (lookup : Completed.CastLookup) (policy : Policy) :
    Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan Configuration where
  Edge := { endpoints : Configuration × Configuration // Step dispatch lookup policy endpoints.1 endpoints.2 }
  source edge := edge.1.1
  target edge := edge.1.2

/-- The finite source policy constructs the actual cast transition beneath
any saved continuation and prior publication prefix. No output-frame witness
or recursive evaluator is supplied by the caller. -/
theorem finite_cast_step
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Policy} {live : List Atom} {scope : List String}
    {value : Entry.Value} {expected : Atom} {activation : Completed.Frame} {raw : ResultSet}
    (finite : policy.matching = .finite)
    (entry : Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .cast)
    (source : TypeCastBatchRel space (activation.read policy value).erase expected activation.bindings raw
      (lookup := lookup (invocationTypeScope scope live (activation.read policy value).erase
        expected activation.bindings) space) (matching := policy.matching.Rel))
    (stack : List Continuation) (emitted : List Result) :
    ∃ results, results.map Completed.rawResult = raw ∧
      Step dispatch lookup policy
        ⟨space,.work (.atom live scope value expected activation),stack,emitted⟩
        ⟨space,.returning results,stack,emitted⟩ := by
  obtain ⟨results,paired⟩ := Completed.CastResultRel.lift_finite_batch finite source
  exact ⟨results,Completed.CastResultRel.readouts paired,.internal (.cast entry source paired)⟩

/-- A finite-policy cast cannot be stuck once its complete type query is
available. The source scan and all output frames are constructed, rather
than supplied as an assumed completed evaluator result. -/
theorem finite_cast_progress
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Policy} {live : List Atom} {scope : List String}
    {value : Entry.Value} {expected : Atom} {activation : Completed.Frame} {types : List Atom}
    (finite : policy.matching = .finite)
    (entry : Entry.Rel policy.reentry (activation.read policy value).status
      (activation.read policy value).erase expected .cast)
    (queried : lookup (invocationTypeScope scope live (activation.read policy value).erase
      expected activation.bindings) space activation.bindings
      (activation.read policy value).erase expected types)
    (stack : List Continuation) (emitted : List Result) :
    ∃ after, Step dispatch lookup policy
      ⟨space,.work (.atom live scope value expected activation),stack,emitted⟩ after := by
  obtain ⟨raw,source⟩ := TypeCastBatchRel.total (space := space)
    (matching := policy.matching.Rel) queried
  obtain ⟨results,_readout,advanced⟩ := finite_cast_step
    (dispatch := dispatch) finite entry source stack emitted
  exact ⟨_,advanced⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldServices)
open RecursiveTasks.Contextual

/-- The existing local evaluator lifted to a single shared world. Ordinary
nodes reuse its primitive logical rules. Context entry stores identities;
each continuing primitive reads its space from the actual reached world.
The native rule installs a locally justified completed host operation; it
neither computes a recursive evaluator reply nor gives a host cost bound. -/
inductive WorldLocalStepWith (admission : Completed.ArgumentService) {Context World : Type} (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) :
    World → Context → Control Context × List Continuation →
    World → Control Context × List Continuation → Prop where
  | core {world label before flatBefore after flatAfter stack remaining} :
      UnscopedControl before flatBefore → managedContextControl before = false →
      LocalStep (admission := admission) (view world label) dispatch lookup policy (flatBefore,stack) (flatAfter,remaining) →
      UnscopedControl after flatAfter →
      WorldLocalStepWith admission view services dispatch lookup policy world label (before,stack) world (after,remaining)
  | context {world afterWorld label childLabel child inner next remaining stack} :
      WorldLocalStepWith admission view services dispatch lookup policy world childLabel (child,inner) afterWorld (next,remaining) →
      WorldLocalStepWith admission view services dispatch lookup policy world label (.context childLabel child inner,stack)
        afterWorld (.context childLabel next remaining,stack)
  | contextReturn {world label childLabel results stack} :
      WorldLocalStepWith admission view services dispatch lookup policy world label (.context childLabel (.returning results) [],stack)
        world (.returning results,stack)
  | evalc {world label childLabel live scope caller readiness operand activation stack} :
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.minimal live scope caller
          (.expression readiness [.symbol "evalc",operand,.grounded (services.contextPayload childLabel)]) activation),stack)
        world (.context childLabel (.work (.invocation live scope caller (activation.read policy operand) activation)) [],stack)
  | metta {world label childLabel live scope caller readiness operand expected activation stack} :
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.minimal live scope caller
          (.expression readiness [.symbol "metta",operand,expected,.grounded (services.contextPayload childLabel)]) activation),stack)
        world (.context childLabel (.work (.atom live scope operand expected.erase activation)) [],stack)
  | contextSpace {world label live scope caller readiness activation stack} :
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.minimal live scope caller (.expression readiness [.symbol "context-space"]) activation),stack)
        world (.returning [(.grounded (services.contextPayload label),activation)],stack)
  | native {world afterWorld label live scope caller readiness name function arguments activation results stack} :
      services.nativeCall label world name.erase function.erase arguments.erase activation results afterWorld →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.minimal live scope caller
          (.expression readiness [.symbol "call-native",name,function,arguments]) activation),stack)
        afterWorld (.returning results,stack)

  | callGroundedDone {world afterWorld label live scope value expected activation operator arguments outcome results stack} :
      value.erase = .expression (operator :: arguments) → dispatch.executable operator → ¬IsErrorRel value.erase →
      services.groundedAt label world live scope activation value outcome afterWorld →
      Completed.NativeOutcomeRel policy dispatch operator arguments value (some expected) activation outcome (.done results) →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.call live scope value expected activation),stack) afterWorld (.returning results,stack)
  | callGroundedResume {world afterWorld label live scope value expected activation operator arguments outcome rows stack} :
      value.erase = .expression (operator :: arguments) → dispatch.executable operator → ¬IsErrorRel value.erase →
      services.groundedAt label world live scope activation value outcome afterWorld →
      Completed.NativeOutcomeRel policy dispatch operator arguments value (some expected) activation outcome (.resume rows) →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.call live scope value expected activation),stack) afterWorld
        (.work (.boundaryBatch live scope none (.native value (some expected) (dispatch.valueProvenance operator arguments)) rows),stack)
  | invocationGroundedDone {world afterWorld label live scope caller value activation operator arguments outcome results stack} :
      value.erase = .expression (operator :: arguments) → dispatch.executable operator →
      services.groundedAt label world live scope activation value outcome afterWorld →
      Completed.NativeOutcomeRel policy dispatch operator arguments value none activation outcome (.done results) →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.invocation live scope caller value activation),stack) afterWorld (.returning results,stack)
  | invocationGroundedResume {world afterWorld label live scope caller value activation operator arguments outcome rows stack} :
      value.erase = .expression (operator :: arguments) → dispatch.executable operator →
      services.groundedAt label world live scope activation value outcome afterWorld →
      Completed.NativeOutcomeRel policy dispatch operator arguments value none activation outcome (.resume rows) →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.invocation live scope caller value activation),stack) afterWorld
        (.work (.boundaryBatch live scope caller (.native value none (dispatch.valueProvenance operator arguments)) rows),stack)

  | collapseEnter {world label live scope caller readiness operand activation snapshots stack} :
      services.snapshots = some snapshots →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.minimal live scope caller (.expression readiness [.symbol "collapse-bind",operand]) activation),stack)
        world (.work (.minimal live scope caller operand activation),.collect activation :: stack)
  | collectEnter {world label rows activation snapshots stack} :
      services.snapshots = some snapshots →
      WorldLocalStepWith admission view services dispatch lookup policy world label (.returning rows,.collect activation :: stack)
        world (.work (.capture rows [] activation),stack)
  | captureNil {world label saved activation snapshots stack} :
      services.snapshots = some snapshots →
      WorldLocalStepWith admission view services dispatch lookup policy world label (.work (.capture [] saved activation),stack)
        world (.returning [(.expression .active saved.reverse,activation)],stack)
  | captureEmpty {world label head tail saved activation snapshots stack} :
      services.snapshots = some snapshots → head.1.erase = Atom.empty →
      WorldLocalStepWith admission view services dispatch lookup policy world label (.work (.capture (head :: tail) saved activation),stack)
        world (.work (.capture tail saved activation),stack)
  | captureOne {world afterWorld label head tail saved activation snapshots payload stack} :
      services.snapshots = some snapshots → head.1.erase ≠ Atom.empty →
      snapshots.capture label world head.2 payload afterWorld →
      WorldLocalStepWith admission view services dispatch lookup policy world label (.work (.capture (head :: tail) saved activation),stack)
        afterWorld (.work (.capture tail (.expression .active [head.1,.grounded payload] :: saved) activation),stack)
  | superposeEnter {world label live scope caller readiness tupleReadiness pairs activation snapshots stack} :
      services.snapshots = some snapshots →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.minimal live scope caller (.expression readiness [.symbol "superpose-bind",.expression tupleReadiness pairs]) activation),stack)
        world (.work (.restore pairs [] activation),stack)
  | restoreNil {world label saved activation snapshots stack} :
      services.snapshots = some snapshots →
      WorldLocalStepWith admission view services dispatch lookup policy world label (.work (.restore [] saved activation),stack)
        world (.returning saved.reverse,stack)
  | restoreOne {world label readiness value payload captured output tail saved activation snapshots stack} :
      services.snapshots = some snapshots → snapshots.restore label world payload captured →
      Completed.Frame.SnapshotMergeRel policy captured activation output →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.restore (.expression readiness [value,.grounded payload] :: tail) saved activation),stack)
        world (.work (.restore tail ((value,output) :: saved) activation),stack)
  | restoreRejected {world label readiness value payload captured tail saved activation snapshots stack} :
      services.snapshots = some snapshots → snapshots.restore label world payload captured →
      (¬∃ output, Spec.Bindings.ScopeObservation.LogicalMergeRel captured.bindings activation.bindings output) →
      WorldLocalStepWith admission view services dispatch lookup policy world label
        (.work (.restore (.expression readiness [value,.grounded payload] :: tail) saved activation),stack)
        world (.work (.restore tail saved activation),stack)

abbrev WorldLocalStep {Context World : Type} (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy)
    (world : World) (label : Context) (before : Control Context × List Continuation)
    (afterWorld : World) (after : Control Context × List Continuation)
    (admission : Completed.ArgumentService := .historical) : Prop :=
  WorldLocalStepWith admission view services dispatch lookup policy world label before afterWorld after

namespace WorldLocalStep
export WorldLocalStepWith (core context contextReturn evalc metta contextSpace native callGroundedDone callGroundedResume invocationGroundedDone invocationGroundedResume collapseEnter collectEnter captureNil captureEmpty captureOne superposeEnter restoreNil restoreOne restoreRejected)
end WorldLocalStep

/-- Global administration retains one world and the root context identity.
Effects reached inside a child return to the enclosing caller in that world;
answer publication keeps the same occurrence history as the old core. -/
inductive WorldStepWith (admission : Completed.ArgumentService) {Context World : Type} (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) :
    WorldConfiguration Context World → WorldConfiguration Context World → Prop where
  | internal {world afterWorld label before after stack remaining emitted} :
      WorldLocalStep (admission := admission) view services dispatch lookup policy world label (before,stack) afterWorld (after,remaining) →
      WorldStepWith admission view services dispatch lookup policy
        ⟨world,label,before,stack,emitted⟩ ⟨afterWorld,label,after,remaining,emitted⟩
  | publish {world label head tail emitted} :
      WorldStepWith admission view services dispatch lookup policy
        ⟨world,label,.returning (head :: tail),[],emitted⟩
        ⟨world,label,.returning tail,[],emitted ++ [head]⟩

abbrev WorldStep {Context World : Type} (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy)
    (before after : WorldConfiguration Context World)
    (admission : Completed.ArgumentService := .historical) : Prop :=
  WorldStepWith admission view services dispatch lookup policy before after

namespace WorldStep
export WorldStepWith (internal publish)
end WorldStep

theorem WorldStep.preserves_context {Context World : Type} {view services dispatch lookup policy}
    {before after : WorldConfiguration Context World}
    (step : WorldStep view services dispatch lookup policy before after) : after.context = before.context := by
  cases step <;> rfl

theorem WorldStep.history_extension {Context World : Type} {view services dispatch lookup policy}
    {before after : WorldConfiguration Context World}
    (step : WorldStep view services dispatch lookup policy before after) :
    ∃ added, after.emitted = before.emitted ++ added := by
  cases step with
  | internal _ => exact ⟨[], (List.append_nil _).symm⟩
  | publish => exact ⟨_, rfl⟩

/-- In the explicit read-only instance, the world extension introduces no
new local behavior. Its context labels are precisely the old space values. -/
theorem world_readOnly_projects {space : Space} {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    {before after : Control × List Continuation} {initial final : Unit}
    (step : WorldLocalStep (fun _ context => context) (WorldServices.readOnly services)
      dispatch lookup policy initial space before final after) :
    LocalStep space dispatch lookup policy before after := by
  induction step with
  | core before _ pureStep after =>
      cases before.same
      cases after.same
      exact pureStep
  | context _ ih => exact .contextStep ih
  | contextReturn => exact .contextReturn
  | evalc => exact .minimalEvalc provided
  | metta => exact .minimalMetta provided
  | contextSpace => exact .minimalContextSpace provided
  | native impossible => cases impossible
  | callGroundedDone _ _ _ produced _ => cases produced
  | callGroundedResume _ _ _ produced _ => cases produced
  | invocationGroundedDone _ _ produced _ => cases produced
  | invocationGroundedResume _ _ produced _ => cases produced

  | collapseEnter unavailable => cases unavailable
  | collectEnter unavailable => cases unavailable
  | captureNil unavailable => cases unavailable
  | superposeEnter unavailable => cases unavailable
  | restoreNil unavailable => cases unavailable
  | captureEmpty unavailable _ => cases unavailable
  | captureOne unavailable _ _ => cases unavailable
  | restoreOne unavailable _ _ => cases unavailable
  | restoreRejected unavailable _ _ => cases unavailable

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual

open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldServices)
open RecursiveTasks.Contextual

/-- Every old local transition is retained by the read-only world instance.
The proof reuses the same ordinary core rules and makes only the three
context instructions and the nested context zipper explicit. -/
theorem world_readOnly_lifts {space : Space} {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    {before after : Control × List Continuation}
    (step : LocalStep space dispatch lookup policy before after) :
    WorldLocalStep (fun _ context => context) (WorldServices.readOnly services)
      dispatch lookup policy () space before () after := by
  have original := step
  induction step
  case contextStep => exact .context (by solve_by_elim)
  case contextReturn => exact .contextReturn
  case minimalEvalc =>
    rename_i actual
    have same := Option.some.inj (actual.symm.trans provided)
    cases same
    exact .evalc
  case minimalMetta =>
    rename_i actual
    have same := Option.some.inj (actual.symm.trans provided)
    cases same
    exact .metta
  case minimalContextSpace =>
    rename_i actual
    have same := Option.some.inj (actual.symm.trans provided)
    cases same
    exact .contextSpace
  all_goals
    apply WorldLocalStep.core
    · constructor
    · first
      | rfl
      | unfold managedContextControl
        split <;> simp_all [Minimal.embeddedInstruction, Entry.Value.erase]
    · exact original
    · constructor

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual

open Spec.Eval
open Spec.Eval.Completed (Policy Result WorldServices)
open RecursiveTasks.Contextual

abbrev WorldSteps {Context World : Type} (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy)
    (before after : WorldConfiguration Context World)
    (admission : Completed.ArgumentService := .historical) : Prop :=
  Relation.ReflTransGen (WorldStep (admission := admission) view services dispatch lookup policy) before after

/-- The world extension uses the same relation-level common-machine boundary
as the existing contextual evaluator. Edges retain their actual world steps. -/
def worldSpan {Context World : Type} (view : World → Context → Space)
    (services : WorldServices Context World) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Policy) :
    Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan (WorldConfiguration Context World) where
  Edge := { endpoints : WorldConfiguration Context World × WorldConfiguration Context World //
    WorldStep view services dispatch lookup policy endpoints.1 endpoints.2 }
  source edge := edge.1.1
  target edge := edge.1.2

/-- Completion still requires an empty root continuation and publication
queue. The reached world remains in the observed configuration. -/
def worldObserve {Context World : Type} (state : WorldConfiguration Context World) : Option (List Result) :=
  match state.control,state.stack with
  | .returning [],[] => some state.emitted
  | _,_ => none

theorem worldObserve_snapshot {Context World : Type} (view : World → Context → Space)
    (state : WorldConfiguration Context World) : observe (state.snapshot view) = worldObserve state := by
  cases state with
  | mk world label control stack emitted =>
      cases control with
      | work => rfl
      | context => rfl
      | returning rows => cases rows <;> cases stack <;> rfl

/-- A pending restore may use another presentation of its caller constraints,
with the exact annotated environment retained. Once restoration returns, the
two executions have identical complete configurations. No other work item or
host callback is identified by this relation. -/
inductive RestoreRepresentation {Context World : Type} :
    WorldConfiguration Context World → WorldConfiguration Context World → Prop where
  | same (state) : RestoreRepresentation state state
  | pending {world label pairs saved caller bindings stack emitted}
      (agreement : BindingSourceAgreement caller.bindings bindings) :
      RestoreRepresentation
        ⟨world,label,.work (.restore pairs saved caller),stack,emitted⟩
        ⟨world,label,.work (.restore pairs saved (caller.represent bindings agreement)),stack,emitted⟩

namespace RestoreRepresentation

theorem symm {Context World : Type} {before after : WorldConfiguration Context World}
    (related : RestoreRepresentation before after) : RestoreRepresentation after before := by
  cases related with
  | same => exact .same _
  | @pending world label pairs saved caller bindings stack emitted agreement =>
      have inverse : (caller.represent bindings agreement).represent caller.bindings agreement.symm = caller := by
        cases caller
        rfl
      have backwards := RestoreRepresentation.pending
        (caller := caller.represent bindings agreement) (bindings := caller.bindings)
        (world := world) (label := label) (pairs := pairs)
        (saved := saved) (stack := stack) (emitted := emitted) agreement.symm
      rw [inverse] at backwards
      exact backwards

/-- Each actual transition is matched by one actual transition, with the same
world and publication history. Rejection uses logical inconsistency; no new
readout representative or completion hypothesis is supplied. -/
theorem step {admission : Completed.ArgumentService} {Context World : Type} {view : World → Context → Space}
    {services dispatch lookup policy} {before target after : WorldConfiguration Context World}
    (related : RestoreRepresentation before target)
    (advanced : WorldStep (admission := admission) view services dispatch lookup policy before after) :
    ∃ next, WorldStep (admission := admission) view services dispatch lookup policy target next ∧
      RestoreRepresentation after next := by
  cases related with
  | same => exact ⟨after,advanced,.same _⟩
  | @pending world label pairs saved caller bindings stack emitted agreement =>
      cases advanced with
      | internal localStep =>
          cases localStep with
          | core first _ primitive _ => cases first; cases primitive
          | restoreNil provided => exact ⟨_,.internal (.restoreNil provided),.same _⟩
          | restoreOne provided loaded merged =>
              have transported := (Completed.Frame.SnapshotMergeRel.represent_inputs_iff
                (BindingSourceAgreement.refl _) agreement).mpr merged
              simp only [Completed.Frame.represent_self] at transported
              exact ⟨_,.internal (.restoreOne provided loaded transported),.pending agreement⟩
          | restoreRejected provided loaded impossible =>
              refine ⟨_,.internal (.restoreRejected provided loaded ?_),.pending agreement⟩
              rintro ⟨output,merged⟩
              exact impossible ⟨output,(Spec.Bindings.ScopeObservation.LogicalMergeRel.congr_inputs
                (BindingSourceAgreement.refl _) agreement).mpr merged⟩

theorem steps {admission : Completed.ArgumentService} {Context World : Type} {view : World → Context → Space}
    {services dispatch lookup policy} {before target after : WorldConfiguration Context World}
    (related : RestoreRepresentation before target)
    (path : WorldSteps (admission := admission) view services dispatch lookup policy before after) :
    ∃ next, WorldSteps (admission := admission) view services dispatch lookup policy target next ∧
      RestoreRepresentation after next := by
  induction path generalizing target with
  | refl => exact ⟨target,.refl,related⟩
  | tail _ advanced ih =>
      obtain ⟨middle,initialPath,atMiddle⟩ := ih related
      obtain ⟨next,last,atNext⟩ := atMiddle.step advanced
      exact ⟨next,initialPath.tail last,atNext⟩

theorem pending_read {Context World : Type} {world : World} {label : Context}
    {pairs saved caller represented stack emitted}
    (related : RestoreRepresentation
      ⟨world,label,.work (.restore pairs saved caller),stack,emitted⟩
      ⟨world,label,.work (.restore pairs saved represented),stack,emitted⟩)
    (policy : Policy) (value : Entry.Value) : represented.read policy value = caller.read policy value := by
  cases related <;> rfl

theorem observe {Context World : Type} {before after : WorldConfiguration Context World}
    (related : RestoreRepresentation before after) : worldObserve before = worldObserve after := by
  cases related <;> rfl

theorem world_eq {Context World : Type} {before after : WorldConfiguration Context World}
    (related : RestoreRepresentation before after) : before.world = after.world := by
  cases related <;> rfl

/-- A finished configuration cannot still be in the representation-changing
phase. In particular, matching only the erased final answer is unnecessary. -/
theorem completed_eq {Context World : Type} {before after : WorldConfiguration Context World}
    (related : RestoreRepresentation before after) (completed : worldObserve before ≠ none) :
    after = before := by
  cases related with
  | same => rfl
  | pending => exact False.elim (completed rfl)

/-- Complete runs agree in both directions, while `steps` supplies the
related residual at every earlier pause. This compares the actual world
machine and preserves its entire finished configuration. -/
theorem completed_paths_iff {Context World : Type} {view : World → Context → Space}
    {services dispatch lookup policy} {before target final : WorldConfiguration Context World}
    (related : RestoreRepresentation before target) (completed : worldObserve final ≠ none) :
    WorldSteps view services dispatch lookup policy before final ↔
      WorldSteps view services dispatch lookup policy target final := by
  constructor
  · intro path
    obtain ⟨next,transported,atNext⟩ := related.steps path
    rw [atNext.completed_eq completed] at transported
    exact transported
  · intro path
    obtain ⟨next,transported,atNext⟩ := related.symm.steps path
    rw [atNext.completed_eq completed] at transported
    exact transported

end RestoreRepresentation

theorem world_readOnly_step_lifts {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    {before after : Configuration} (step : Step dispatch lookup policy before after) :
    WorldStep (fun (_ : Unit) => id) (WorldServices.readOnly services) dispatch lookup policy
      (WorldConfiguration.ofReadOnly before) (WorldConfiguration.ofReadOnly after) := by
  cases step with
  | internal localStep => exact .internal (world_readOnly_lifts provided localStep)
  | publish => exact .publish

theorem world_readOnly_step_projects {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    {before after : WorldConfiguration Space Unit}
    (step : WorldStep (fun (_ : Unit) => id) (WorldServices.readOnly services) dispatch lookup policy before after) :
    Step dispatch lookup policy (before.snapshot (fun _ => id)) (after.snapshot (fun _ => id)) := by
  cases step with
  | internal localStep =>
      simp only [WorldConfiguration.snapshot, Control.mapContexts_id]
      exact .internal (world_readOnly_projects provided localStep)
  | publish => exact .publish

theorem world_readOnly_steps_lift {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    {before after : Configuration} (path : Steps dispatch lookup policy before after) :
    WorldSteps (fun (_ : Unit) => id) (WorldServices.readOnly services) dispatch lookup policy
      (WorldConfiguration.ofReadOnly before) (WorldConfiguration.ofReadOnly after) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (world_readOnly_step_lifts provided step)

theorem world_readOnly_steps_project {services : Minimal.Services} {enumeration : Minimal.Enumeration}
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Policy}
    (provided : dispatch.minimal = some ⟨services,enumeration⟩)
    {before after : WorldConfiguration Space Unit}
    (path : WorldSteps (fun (_ : Unit) => id) (WorldServices.readOnly services) dispatch lookup policy before after) :
    Steps dispatch lookup policy (before.snapshot (fun _ => id)) (after.snapshot (fun _ => id)) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (world_readOnly_step_projects provided step)

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual

open Spec.Eval.Completed (WorldEnvironment)
open RecursiveTasks.Contextual

/-- Finite local blocks keep the actual world at both endpoints. -/
abbrev WorldLocalSteps {Context World : Type}
    (environment : WorldEnvironment Context World) (policy : Spec.Eval.Completed.Policy) (label : Context)
    (world : World) (before : Control Context × List Continuation)
    (afterWorld : World) (after : Control Context × List Continuation) : Prop :=
  Relation.ReflTransGen
    (fun first last : World × (Control Context × List Continuation) =>
      WorldLocalStep (admission := environment.arguments) environment.view environment.services environment.dispatch environment.lookup policy
        first.1 label first.2 last.1 last.2) (world,before) (afterWorld,after)

theorem worldObserve_eq_some {Context World : Type}
    {state : WorldConfiguration Context World} {answers : List Spec.Eval.Completed.Result}
    (observed : worldObserve state = some answers) :
    state = ⟨state.world,state.context,.returning [],[],answers⟩ := by
  cases state with
  | mk world label control stack emitted =>
      cases control with
      | work => simp [worldObserve] at observed
      | context => simp [worldObserve] at observed
      | returning results =>
          cases results <;> cases stack <;> simp_all [worldObserve]

/-- A fully published root cannot execute a native operation again. -/
theorem world_observed_final {Context World : Type} {view services dispatch lookup policy}
    {state : WorldConfiguration Context World} {answers : List Spec.Eval.Completed.Result}
    (observed : worldObserve state = some answers) :
    ¬∃ after, WorldStep view services dispatch lookup policy state after := by
  rw [worldObserve_eq_some observed]
  rintro ⟨after,advanced⟩
  cases advanced with
  | internal edge =>
      cases edge with
      | core first _ primitive _ => cases first; cases primitive

/-- A producer-completed raw value has one return transition. Its syntax
cannot select a function-body frame or invoke its producer again. -/
theorem native_completed_raw_exact {Context World : Type} {view services dispatch lookup policy}
    {world afterWorld : World} {label : Context} {live scope caller original value activation stack}
    {after : Control Context} {remaining : List Continuation}
    (advanced : WorldLocalStep view services dispatch lookup policy world label
      (.work (.boundary live scope caller (.native original none .completed) value activation),stack)
      afterWorld (after,remaining)) :
    afterWorld = world ∧ after = .returning [(value,activation)] ∧ remaining = stack := by
  cases advanced with
  | core first _ primitive last =>
      cases first
      cases primitive
      cases last
      exact ⟨rfl,rfl,rfl⟩

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual


namespace Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval
open Spec.Type Spec.Eval.Steps
open Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.ScopeObservation
open Spec.Bindings.ScopeObservation
open RecursiveTasks.Contextual
open Mettapedia.Machines.OrderedProtocol.Completion

/-! ## Simultaneous Variable Renaming for Contextual Machine Steps and Observations -/

@[simp] theorem load_rename (p : Equiv.Perm String) (space : Space) (value expected : Atom) :
    (load space value expected).rename p =
      load (Spec.Eval.Renaming.space p space) (renameTypeVars p value) (renameTypeVars p expected) := by
  simp [load, Task.rename, Entry.Value.rename_ofAtom]

@[simp] theorem observe_rename (p : Equiv.Perm String) (state : Configuration) :
    observe (state.rename p) = (observe state).map (List.map (Completed.Result.rename p)) := by
  rcases state with ⟨space, control, stack, emitted⟩
  cases control with
  | work task => simp [observe, Configuration.rename, Control.rename]
  | context label child inner => simp [observe, Configuration.rename, Control.rename]
  | returning results =>
      cases results <;> cases stack <;>
        simp [observe, Configuration.rename, Control.rename]

theorem observe_rename_some_iff (p : Equiv.Perm String) (state : Configuration)
    (answers : List Completed.Result) :
    observe (state.rename p) = some (answers.map (Completed.Result.rename p)) ↔
      observe state = some answers := by
  rw [observe_rename]
  cases h : observe state with
  | none => simp
  | some actual =>
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · intro eq
        have inv := congrArg (List.map (Completed.Result.rename p.symm)) eq
        simpa [List.map_map, Function.comp_def] using inv
      · rintro rfl
        rfl

private theorem zip_argumentRequest_rename (p : Equiv.Perm String)
    (values : List Entry.Value) (types : List Atom) :
    (values.zip types).map (Completed.ArgumentRequest.rename p) =
      (values.map (Entry.Value.rename p)).zip (types.map (renameTypeVars p)) := by
  induction values generalizing types with
  | nil => simp
  | cons v vs ih =>
      cases types with
      | nil => simp
      | cons t ts =>
          simp [Completed.ArgumentRequest.rename, ih]

theorem LocalStep.rename (p : Equiv.Perm String)
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {lookup : Completed.CastLookup} {policy : Completed.Policy}
    {before after : Control × List Continuation}
    (step : LocalStep space dispatch lookup policy before after) :
    LocalStep (Spec.Eval.Renaming.space p space) (Spec.Eval.Renaming.dispatch p dispatch)
      (Completed.renameCastLookup p lookup) policy
      (before.1.rename p, before.2.map (Continuation.rename p))
      (after.1.rename p, after.2.map (Continuation.rename p)) := by
  induction step with
  | @delivered space dispatch lookup policy live scope value expected activation stack entered =>
      have enteredRenamed :
          Entry.Rel policy.reentry
            ((activation.rename p).read policy (value.rename p)).status
            ((activation.rename p).read policy (value.rename p)).erase
            (renameTypeVars p expected) .deliver := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_status,
          Entry.Value.rename_erase] using entered.rename p
      simpa only [Control.rename, Task.rename, List.map_cons, List.map_nil,
        Completed.Result.rename, Completed.Frame.read_rename] using
        LocalStep.delivered enteredRenamed
  | @cast space dispatch lookup policy live scope value expected activation raw results stack
      entered batch paired =>
      have enteredRenamed :
          Entry.Rel policy.reentry
            ((activation.rename p).read policy (value.rename p)).status
            ((activation.rename p).read policy (value.rename p)).erase
            (renameTypeVars p expected) .cast := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_status,
          Entry.Value.rename_erase] using entered.rename p
      have batchRenamed :
          TypeCastBatchRel (Spec.Eval.Renaming.space p space)
            ((activation.rename p).read policy (value.rename p)).erase
            (renameTypeVars p expected)
            (activation.rename p).bindings
            (Spec.Eval.Renaming.results p raw)
            (lookup := Completed.renameCastLookup p lookup
              (invocationTypeScope (scope.map p) (live.map (renameTypeVars p))
                ((activation.rename p).read policy (value.rename p)).erase
                (renameTypeVars p expected) (activation.rename p).bindings)
              (Spec.Eval.Renaming.space p space))
            (matching := policy.matching.Rel) := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_erase,
          Completed.Frame.rename_bindings, Spec.Eval.Renaming.invocation_scope,
          Completed.renameCastLookup_apply] using batch.rename p
      have pairedRaw :
          List.Forall₂
            (Completed.CastResultRel policy
              (Completed.renameTypeLookup p
                (lookup (invocationTypeScope scope live (activation.read policy value).erase
                  expected activation.bindings) space))
              (activation.rename p) ((activation.read policy value).rename p)
              (renameTypeVars p expected))
            (Spec.Eval.Renaming.results p raw)
            (results.map (Completed.Result.rename p)) := by
        change List.Forall₂ _ (raw.map (Spec.Eval.Renaming.result p))
          (results.map (Completed.Result.rename p))
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        exact paired.imp (fun _ _ item => item.rename p)
      have pairedRenamed :
          List.Forall₂
            (Completed.CastResultRel policy
              (Completed.renameCastLookup p lookup
                (invocationTypeScope (scope.map p) (live.map (renameTypeVars p))
                  ((activation.rename p).read policy (value.rename p)).erase
                  (renameTypeVars p expected) (activation.rename p).bindings)
                (Spec.Eval.Renaming.space p space))
              (activation.rename p) ((activation.rename p).read policy (value.rename p))
              (renameTypeVars p expected))
            (Spec.Eval.Renaming.results p raw)
            (results.map (Completed.Result.rename p)) := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_erase,
          Completed.Frame.rename_bindings, Spec.Eval.Renaming.invocation_scope,
          Completed.renameCastLookup_apply] using pairedRaw
      exact LocalStep.cast enteredRenamed batchRenamed pairedRenamed
  | @atomTuple space dispatch lookup policy live scope value expected activation readiness
      operator arguments stack entered shaped typed =>
      have enteredRenamed :
          Entry.Rel policy.reentry
            ((activation.rename p).read policy (value.rename p)).status
            ((activation.rename p).read policy (value.rename p)).erase
            (renameTypeVars p expected) .interpret := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_status,
          Entry.Value.rename_erase] using entered.rename p
      have shapedRenamed :
          (activation.rename p).read policy (value.rename p) =
            .expression readiness (operator.rename p :: arguments.map (Entry.Value.rename p)) := by
        rw [Completed.Frame.read_rename, shaped]
        simp
      have typedRenamed :
          TypeOccurrencesRel (Spec.Eval.Renaming.space p space).atoms (operator.rename p).erase
            {Atom.undefinedType} := by
        simpa only [Entry.Value.rename_erase, Multiset.map_singleton,
          Atom.undefinedType, Spec.Eval.Renaming.atom_symbol] using typed.rename p
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.Frame.read_rename, Entry.Value.rename_erase] using
        LocalStep.atomTuple enteredRenamed shapedRenamed typedRenamed
  | @atomFunction space dispatch lookup policy live scope value expected activation readiness
      operator arguments signature frames stack entered shaped selected =>
      have enteredRenamed :
          Entry.Rel policy.reentry
            ((activation.rename p).read policy (value.rename p)).status
            ((activation.rename p).read policy (value.rename p)).erase
            (renameTypeVars p expected) .interpret := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_status,
          Entry.Value.rename_erase] using entered.rename p
      have shapedRenamed :
          (activation.rename p).read policy (value.rename p) =
            .expression readiness (operator.rename p :: arguments.map (Entry.Value.rename p)) := by
        rw [Completed.Frame.read_rename, shaped]
        simp
      have selectedRenamed :
          Completed.InvocationSelectionRel (Spec.Eval.Renaming.space p space)
            (Completed.renameCastLookup p lookup) policy
            (live.map (renameTypeVars p)) (scope.map p)
            ((activation.rename p).read policy (value.rename p)).erase
            (operator.rename p).erase (renameTypeVars p expected) (activation.rename p)
            (.selected (Spec.Eval.Renaming.policy p signature)
              (frames.map (Completed.Frame.rename p))) := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_erase,
          Completed.InvocationSelection.rename] using selected.rename p
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.Frame.read_rename, Entry.Value.rename_erase] using
        LocalStep.atomFunction (admission := .historical) enteredRenamed shapedRenamed selectedRenamed
  | @atomFallback space dispatch lookup policy live scope value expected activation readiness
      operator arguments errors stack entered shaped selected =>
      have enteredRenamed :
          Entry.Rel policy.reentry
            ((activation.rename p).read policy (value.rename p)).status
            ((activation.rename p).read policy (value.rename p)).erase
            (renameTypeVars p expected) .interpret := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_status,
          Entry.Value.rename_erase] using entered.rename p
      have shapedRenamed :
          (activation.rename p).read policy (value.rename p) =
            .expression readiness (operator.rename p :: arguments.map (Entry.Value.rename p)) := by
        rw [Completed.Frame.read_rename, shaped]
        simp
      have selectedRenamed :
          Completed.InvocationSelectionRel (Spec.Eval.Renaming.space p space)
            (Completed.renameCastLookup p lookup) policy
            (live.map (renameTypeVars p)) (scope.map p)
            ((activation.rename p).read policy (value.rename p)).erase
            (operator.rename p).erase (renameTypeVars p expected) (activation.rename p)
            (.exhausted (errors.map (renameTypeVars p)) true) := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_erase,
          Completed.InvocationSelection.rename] using selected.rename p
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.Frame.read_rename, Entry.Value.rename_erase] using
        LocalStep.atomFallback (admission := .historical) enteredRenamed shapedRenamed selectedRenamed
  | @atomSelectionFailed space dispatch lookup policy live scope value expected activation readiness
      operator arguments errors stack entered shaped selected =>
      have enteredRenamed :
          Entry.Rel policy.reentry
            ((activation.rename p).read policy (value.rename p)).status
            ((activation.rename p).read policy (value.rename p)).erase
            (renameTypeVars p expected) .interpret := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_status,
          Entry.Value.rename_erase] using entered.rename p
      have shapedRenamed :
          (activation.rename p).read policy (value.rename p) =
            .expression readiness (operator.rename p :: arguments.map (Entry.Value.rename p)) := by
        rw [Completed.Frame.read_rename, shaped]
        simp
      have selectedRenamed :
          Completed.InvocationSelectionRel (Spec.Eval.Renaming.space p space)
            (Completed.renameCastLookup p lookup) policy
            (live.map (renameTypeVars p)) (scope.map p)
            ((activation.rename p).read policy (value.rename p)).erase
            (operator.rename p).erase (renameTypeVars p expected) (activation.rename p)
            (.exhausted (errors.map (renameTypeVars p)) false) := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_erase,
          Completed.InvocationSelection.rename] using selected.rename p
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.Frame.read_rename, Entry.Value.rename_erase,
        Completed.diagnosticResults_rename] using
        LocalStep.atomSelectionFailed (admission := .historical) enteredRenamed shapedRenamed selectedRenamed
  | tupleNil =>
      simpa [Control.rename, Task.rename, Completed.Result.rename] using LocalStep.tupleNil
  | tupleSingleton =>
      simpa [Control.rename, Task.rename, Continuation.rename, Atom.undefinedType] using
        LocalStep.tupleSingleton
  | @tupleCons _ _ _ _ live scope head second remaining activation stack =>
      simpa [Control.rename, Task.rename, Continuation.rename, Atom.undefinedType,
        List.map_map, Function.comp_def, Entry.Value.rename_erase] using
        (LocalStep.tupleCons (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (head := head.rename p) (second := second.rename p)
          (remaining := remaining.map (Entry.Value.rename p))
          (activation := activation.rename p) (stack := stack.map (Continuation.rename p)))
  | branchesNil => exact .branchesNil
  | @branchesStopped _ _ _ _ _ _ _ head _ _ stopped =>
      have stoppedRenamed : IsEmptyOrErrorRel (Completed.Result.rename p head).1.erase := by
        simpa only [Completed.Result.rename_fst, Entry.Value.rename_erase,
          Spec.Eval.Renaming.stopped_iff] using stopped
      exact .branchesStopped stoppedRenamed
  | @branchesContinue _ _ _ _ _ _ _ head _ _ notStopped =>
      have notStoppedRenamed : ¬IsEmptyOrErrorRel (Completed.Result.rename p head).1.erase := by
        simpa only [Completed.Result.rename_fst, Entry.Value.rename_erase,
          Spec.Eval.Renaming.stopped_iff] using notStopped
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.Result.rename_fst, Completed.Result.rename_snd,
        Entry.Value.rename_erase] using
        LocalStep.branchesContinue notStoppedRenamed
  | argumentsNil =>
      simpa [Control.rename, Task.rename, Completed.Result.rename,
        Entry.Value.argumentPacket] using LocalStep.argumentsNil
  | @argumentsCons _ _ _ _ live scope request requests activation stack =>
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        List.map_append, Completed.argumentScope_rename,
        Completed.ArgumentRequest.rename_fst, Completed.ArgumentRequest.rename_snd] using
        (LocalStep.argumentsCons (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (request := Completed.ArgumentRequest.rename p request)
          (requests := requests.map (Completed.ArgumentRequest.rename p))
          (activation := activation.rename p) (stack := stack.map (Continuation.rename p)))
  | argumentBranchesNil => exact .argumentBranchesNil
  | @argumentBranchesStopped _ _ _ _ _ _ original _ head _ _ stopped =>
      exact .argumentBranchesStopped
        ((Completed.ArgumentStopped.rename_iff p original head).mpr stopped)
  | @argumentBranchesContinue _ _ _ _ _ _ original _ head _ _ notStopped =>
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.Result.rename_fst, Completed.Result.rename_snd,
        Entry.Value.rename_erase] using
        LocalStep.argumentBranchesContinue
          (mt (Completed.ArgumentStopped.rename_iff p original head).mp notStopped)
  | @functionStart _ _ _ _ live scope expected signature operator arguments activation stack
      sameLen =>
      have sameLenRenamed :
          (arguments.map (Entry.Value.rename p)).length =
            (Spec.Eval.Renaming.policy p signature).argumentTypes.length := by
        simpa [Spec.Eval.Renaming.policy] using sameLen
      have scopeEq :
          expectedApplicationScope
            (.expression (renameTypeVars p operator.erase ::
              arguments.map (fun x => renameTypeVars p x.erase)))
            (renameTypeVars p expected) =
            (expectedApplicationScope
              (.expression (operator.erase :: arguments.map Entry.Value.erase))
              expected).map p := by
        have exprEq :
            Atom.expression (renameTypeVars p operator.erase ::
              arguments.map (fun x => renameTypeVars p x.erase)) =
            renameTypeVars p (.expression (operator.erase :: arguments.map Entry.Value.erase)) := by
          simp [List.map_map, Function.comp_def]
        rw [exprEq, Spec.Eval.Renaming.scope]
      simpa [Control.rename, Task.rename, Continuation.rename, Spec.Eval.Renaming.policy,
        List.map_map, Function.comp_def, Entry.Value.rename_erase, scopeEq,
        zip_argumentRequest_rename] using
        (LocalStep.functionStart (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (expected := renameTypeVars p expected) (operator := operator.rename p)
          (activation := activation.rename p) (stack := stack.map (Continuation.rename p))
          sameLenRenamed)
  | functionBranchesNil => exact .functionBranchesNil
  | @functionBranchesStopped _ _ _ _ _ _ _ head _ _ stopped =>
      have stoppedRenamed : IsEmptyOrErrorRel (Completed.Result.rename p head).1.erase := by
        simpa only [Completed.Result.rename_fst, Entry.Value.rename_erase,
          Spec.Eval.Renaming.stopped_iff] using stopped
      exact .functionBranchesStopped stoppedRenamed
  | @functionBranchesContinue _ _ _ _ _ _ _ head _ _ notStopped =>
      have notStoppedRenamed : ¬IsEmptyOrErrorRel (Completed.Result.rename p head).1.erase := by
        simpa only [Completed.Result.rename_fst, Entry.Value.rename_erase,
          Spec.Eval.Renaming.stopped_iff] using notStopped
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.Result.rename_fst, Completed.Result.rename_snd,
        Entry.Value.rename_erase] using
        LocalStep.functionBranchesContinue notStoppedRenamed
  | invocationsNil => exact .invocationsNil
  | @invocationsCons _ _ _ _ live scope expected signature operator arguments activation activations stack =>
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Completed.invocationReturnType_rename] using
        (LocalStep.invocationsCons (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (expected := renameTypeVars p expected) (signature := Spec.Eval.Renaming.policy p signature)
          (operator := operator.rename p) (arguments := arguments.map (Entry.Value.rename p))
          (activation := activation.rename p) (activations := activations.map (Completed.Frame.rename p))
          (stack := stack.map (Continuation.rename p)))
  | callsNil => exact .callsNil
  | callsCons => exact .callsCons
  | @callError _ _ _ _ _ _ value _ _ _ isErr =>
      exact .callError
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.error_iff] using isErr)
  | @callEmbedded _ _ _ _ _ _ value _ _ _ notErr notHost isEmb =>
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Option.map_none, Completed.Boundary.rename] using
        LocalStep.callEmbedded
          (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.error_iff] using notErr)
          (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.host_call] using notHost)
          (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.embedded] using isEmb)
  | @callAbsent _ _ _ _ _ _ value _ _ _ notErr ordinary frontier =>
      exact .callAbsent
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.error_iff] using notErr)
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.nonGrounded_call] using ordinary)
        (by simpa only [List.map_cons, Entry.Value.rename_erase,
          Completed.Frame.rename_bindings, List.map_nil] using frontier.rename p)
  | @callEquations _ _ _ _ _ _ value _ _ works _ notErr ordinary frontier nonEmpty =>
      exact .callEquations
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.error_iff] using notErr)
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.nonGrounded_call] using ordinary)
        (by simpa only [List.map_cons, Entry.Value.rename_erase,
          Completed.Frame.rename_bindings] using frontier.rename p)
        (by simpa using nonEmpty)
  | equationsNil => exact .equationsNil
  | @equationsCons _ _ _ policy live scope original expected activation work works output stack
      sameBindings unified =>
      have sameBindingsRenamed :
          (output.rename p).bindings = (work.rename p).bindings := by
        simpa only [Completed.Frame.rename_bindings, Spec.Eval.Steps.EquationWork.rename] using
          congrArg (renameBindings p) sameBindings
      have unifiedRenamed :
          Entry.Value.UnifyRel policy.rebuilding (activation.rename p).environment
            (original.rename p) (Entry.Value.ofAtom (work.rename p).pattern)
            (output.rename p).environment := by
        simpa only [Completed.Frame.rename_environment, Spec.Eval.Steps.EquationWork.rename,
          Entry.Value.rename_ofAtom] using Entry.Value.UnifyRel.rename p unified
      have bodyRead :
          (output.rename p).read policy (Entry.Value.ofAtom (renameTypeVars p work.body)) =
            (output.read policy (Entry.Value.ofAtom work.body)).rename p := by
        rw [← Entry.Value.rename_ofAtom, Completed.Frame.read_rename]
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Option.map_some, Option.map_none, Entry.Value.rename_erase, Completed.Boundary.rename,
        Spec.Eval.Steps.EquationWork.rename, bodyRead] using
        (LocalStep.equationsCons (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (expected := renameTypeVars p expected) (work := work.rename p)
          (works := works.map (Spec.Eval.Steps.EquationWork.rename p))
          (stack := stack.map (Continuation.rename p)) sameBindingsRenamed unifiedRenamed)
  | @returnRefused _ _ _ _ _ _ _ _ value _ _ refused =>
      have hRefused : (value.rename p).erase = Atom.notReducible := by
        rw [Entry.Value.rename_erase, refused, Spec.Eval.Renaming.atom_notReducible]
      exact .returnRefused hRefused
  | @returnStopped _ _ _ _ _ _ _ _ value _ _ stopped =>
      have hStopped : IsEmptyOrErrorRel (value.rename p).erase := by
        simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.stopped_iff] using stopped
      exact .returnStopped hStopped
  | @returnEvaluate _ _ _ _ _ _ _ _ value _ _ notRefused notStopped =>
      have hNotRefused : (value.rename p).erase ≠ Atom.notReducible := by
        rw [Entry.Value.rename_erase, ← Spec.Eval.Renaming.atom_notReducible]
        exact mt (Spec.Eval.Renaming.atoms_equal p value.erase Atom.notReducible).mp notRefused
      have hNotStopped : ¬IsEmptyOrErrorRel (value.rename p).erase := by
        simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.stopped_iff] using notStopped
      exact .returnEvaluate hNotRefused hNotStopped
  | @minimalData _ _ _ _ _ _ _ value _ _ isData =>
      exact .minimalData
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.embedded] using isData)
  | @minimalEval _ _ _ _ live scope caller readiness operand activation stack =>
      simpa [Control.rename, Task.rename, Completed.Frame.read_rename] using
        (LocalStep.minimalEval (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (readiness := readiness)
          (operand := operand.rename p) (activation := activation.rename p)
          (stack := stack.map (Continuation.rename p)))
  | @minimalEvalc space context dispatch lookup policy live scope caller readiness operand
      activation services enumeration stack provided =>
      have hostProvided := Spec.Eval.Renaming.minimal_host p dispatch ⟨services, enumeration⟩ provided
      simpa [Control.rename, Task.rename, Completed.Frame.read_rename,
        Spec.Eval.Renaming.host, Spec.Eval.Renaming.context_payload p services context] using
        (LocalStep.minimalEvalc (context := Spec.Eval.Renaming.space p context)
          (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (readiness := readiness)
          (operand := operand.rename p) (activation := activation.rename p)
          (stack := stack.map (Continuation.rename p)) hostProvided)
  | @minimalChain _ _ _ _ live scope caller readiness operand name template activation stack =>
      simpa [Control.rename, Task.rename, Continuation.rename, Completed.Boundary.rename,
        Entry.Value.rename_erase] using
        (LocalStep.minimalChain (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (readiness := readiness)
          (operand := operand.rename p) (name := p name) (template := template.rename p)
          (activation := activation.rename p) (stack := stack.map (Continuation.rename p)))
  | @minimalUnifyYes _ _ _ _ live scope caller readiness target pattern yes no activation output stack
      candidate unified =>
      have candRenamed :
          UnifyCandidateRel (target.rename p).erase (pattern.rename p).erase
            (activation.rename p).bindings (output.rename p).bindings := by
        simpa only [Entry.Value.rename_erase, Completed.Frame.rename_bindings] using
          Spec.Eval.Renaming.unify_candidate p candidate
      simpa [Control.rename, Task.rename, Completed.Result.rename,
        Completed.Frame.read_rename] using
        (LocalStep.minimalUnifyYes (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (readiness := readiness)
          (yes := yes.rename p) (no := no.rename p) (stack := stack.map (Continuation.rename p))
          candRenamed (Entry.Value.UnifyRel.rename p unified))
  | @minimalUnifyNo _ _ _ _ _ _ _ _ target pattern yes no activation _ noMatch =>
      simpa [Control.rename, Task.rename, Completed.Result.rename] using
        LocalStep.minimalUnifyNo
          (by simpa only [Entry.Value.rename_erase, Completed.Frame.rename_bindings] using
            Spec.Eval.Renaming.unify_no_match p noMatch)
  | @minimalUnifyBadArity _ dispatch _ _ _ _ _ _ tail activation _ badLen =>
      have badLenRenamed : (tail.map (Entry.Value.rename p)).length ≠ 4 := by
        simpa using badLen
      have exprEq :
          renameTypeVars p (.expression (.symbol "unify" :: tail.map Entry.Value.erase)) =
            .expression (.symbol "unify" :: (tail.map (Entry.Value.rename p)).map Entry.Value.erase) := by
        simp [List.map_map, Function.comp_def, Entry.Value.rename_erase]
      have errEq := Spec.Eval.Renaming.malformed_call_error p dispatch
        (.expression (.symbol "unify" :: tail.map Entry.Value.erase))
      rw [exprEq] at errEq
      simpa [Control.rename, Task.rename, Completed.Result.rename, Entry.Value.rename_ofAtom,
        ← errEq] using
        LocalStep.minimalUnifyBadArity (tail := tail.map (Entry.Value.rename p)) badLenRenamed
  | minimalConsAtom =>
      simpa [Control.rename, Task.rename, Completed.Result.rename] using LocalStep.minimalConsAtom
  | minimalDeconsAtom =>
      simpa [Control.rename, Task.rename, Completed.Result.rename] using LocalStep.minimalDeconsAtom
  | @minimalFunction _ _ _ _ _ _ _ _ body bodyReadiness children _ _ shaped =>
      have shapedRenamed :
          body.rename p = .expression bodyReadiness (children.map (Entry.Value.rename p)) := by
        rw [shaped]
        simp
      simpa [Control.rename, Task.rename, Continuation.rename, Completed.Boundary.rename,
        Entry.Value.rename_erase] using LocalStep.minimalFunction shapedRenamed
  | @minimalMetta space context dispatch lookup policy live scope caller readiness operand
      expected activation services enumeration stack provided =>
      have hostProvided := Spec.Eval.Renaming.minimal_host p dispatch ⟨services, enumeration⟩ provided
      simpa [Control.rename, Task.rename, Entry.Value.rename_erase,
        Spec.Eval.Renaming.host, Spec.Eval.Renaming.context_payload p services context] using
        (LocalStep.minimalMetta (context := Spec.Eval.Renaming.space p context)
          (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (readiness := readiness)
          (operand := operand.rename p) (expected := expected.rename p)
          (activation := activation.rename p) (stack := stack.map (Continuation.rename p))
          hostProvided)
  | @minimalContextSpace space dispatch lookup policy live scope caller readiness activation
      services enumeration stack provided =>
      have hostProvided := Spec.Eval.Renaming.minimal_host p dispatch ⟨services, enumeration⟩ provided
      simpa [Control.rename, Task.rename, Completed.Result.rename,
        Spec.Eval.Renaming.host, Spec.Eval.Renaming.context_payload p services space] using
        (LocalStep.minimalContextSpace (space := Spec.Eval.Renaming.space p space)
          (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (readiness := readiness)
          (activation := activation.rename p) (stack := stack.map (Continuation.rename p))
          hostProvided)
  | bodyStart =>
      simpa [Control.rename, Task.rename, Continuation.rename, Completed.Boundary.rename] using
        LocalStep.bodyStart
  | @invocationEmbedded _ _ _ _ _ _ _ value _ _ notHost isEmb =>
      exact .invocationEmbedded
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.host_call] using notHost)
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.embedded] using isEmb)
  | @invocationAbsent _ _ _ _ _ _ _ value _ _ ordinary frontier =>
      simpa [Control.rename, Task.rename, Completed.Result.rename] using
        LocalStep.invocationAbsent
          (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.nonGrounded_call] using ordinary)
          (by simpa only [Entry.Value.rename_erase, Completed.Frame.rename_bindings,
            List.map_nil] using frontier.rename p)
  | @invocationEquations _ _ _ _ _ _ _ value _ works _ ordinary frontier nonEmpty =>
      exact .invocationEquations
        (by simpa only [Entry.Value.rename_erase, Spec.Eval.Renaming.nonGrounded_call] using ordinary)
        (by simpa only [Entry.Value.rename_erase, Completed.Frame.rename_bindings] using
          frontier.rename p)
        (by simpa using nonEmpty)
  | invocationEquationsNil => exact .invocationEquationsNil
  | @invocationEquationsCons _ _ _ policy live scope original activation work works output stack
      sameBindings unified =>
      have sameBindingsRenamed :
          (output.rename p).bindings = (work.rename p).bindings := by
        simpa only [Completed.Frame.rename_bindings, Spec.Eval.Steps.EquationWork.rename] using
          congrArg (renameBindings p) sameBindings
      have unifiedRenamed :
          Entry.Value.UnifyRel policy.rebuilding (activation.rename p).environment
            (original.rename p) (Entry.Value.ofAtom (work.rename p).pattern)
            (output.rename p).environment := by
        simpa only [Completed.Frame.rename_environment, Spec.Eval.Steps.EquationWork.rename,
          Entry.Value.rename_ofAtom] using Entry.Value.UnifyRel.rename p unified
      have bodyRead :
          (output.rename p).read policy (Entry.Value.ofAtom (renameTypeVars p work.body)) =
            (output.read policy (Entry.Value.ofAtom work.body)).rename p := by
        rw [← Entry.Value.rename_ofAtom, Completed.Frame.read_rename]
      simpa only [Control.rename, Task.rename, Continuation.rename, List.map_cons,
        Option.map_some, Entry.Value.rename_erase, Completed.Boundary.rename,
        Spec.Eval.Steps.EquationWork.rename, bodyRead] using
        (LocalStep.invocationEquationsCons (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (work := work.rename p) (works := works.map (Spec.Eval.Steps.EquationWork.rename p))
          (stack := stack.map (Continuation.rename p)) sameBindingsRenamed unifiedRenamed)
  | @boundaryChain _ _ _ _ live scope caller name template value activation stack =>
      simpa [Control.rename, Task.rename, Completed.Boundary.rename,
        Completed.Frame.read_rename, Completed.substituteBinder_rename] using
        (LocalStep.boundaryChain (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (name := p name) (template := template.rename p)
          (value := value.rename p) (activation := activation.rename p)
          (stack := stack.map (Continuation.rename p)))
  | @boundaryBodyTerminal _ _ _ policy live scope caller value activation stack isTerm =>
      have termRenamed :
          Minimal.embeddedInstruction ((activation.rename p).read policy (value.rename p)).erase = false := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_erase,
          Spec.Eval.Renaming.embedded] using isTerm
      simpa [Control.rename, Task.rename, Completed.Boundary.rename, Completed.Result.rename,
        Completed.Frame.read_rename] using
        (LocalStep.boundaryBodyTerminal (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (stack := stack.map (Continuation.rename p))
          termRenamed)
  | @boundaryBodyResume _ _ _ policy live scope caller value activation stack isRes =>
      have resRenamed :
          Minimal.embeddedInstruction ((activation.rename p).read policy (value.rename p)).erase = true := by
        simpa only [Completed.Frame.read_rename, Entry.Value.rename_erase,
          Spec.Eval.Renaming.embedded] using isRes
      simpa [Control.rename, Task.rename, Completed.Boundary.rename,
        Completed.Frame.read_rename] using
        (LocalStep.boundaryBodyResume (live := live.map (renameTypeVars p)) (scope := scope.map p)
          (caller := caller.map (renameTypeVars p)) (stack := stack.map (Continuation.rename p))
          resRenamed)
  | boundaryFunctionReturn =>
      simpa [Control.rename, Task.rename, Completed.Boundary.rename,
        Completed.Result.rename] using LocalStep.boundaryFunctionReturn
  | @boundaryFunctionNoReturn _ _ _ _ _ _ caller value _ _ notRet =>
      have notRetRenamed :
          ∀ returned, (value.rename p).erase ≠ .expression [.symbol "return", returned] := by
        intro returned same
        apply notRet (renameTypeVars p.symm returned)
        have inv := congrArg (renameTypeVars p.symm) same
        simpa [Entry.Value.rename_erase] using inv
      simpa [Control.rename, Task.rename, Completed.Boundary.rename, Completed.Result.rename,
        Entry.Value.rename_ofAtom, Entry.Value.rename_erase,
        Spec.Eval.Renaming.terminal] using
        LocalStep.boundaryFunctionNoReturn notRetRenamed
  | @boundaryProducerRaw _ _ _ policy _ _ _ value _ _ notPending =>
      exact .boundaryProducerRaw
        (mt (Completed.FunctionPending.rename_iff p policy value).mp notPending)
  | @boundaryProducerFunction _ _ _ policy _ _ _ value _ _ isPending =>
      exact .boundaryProducerFunction
        ((Completed.FunctionPending.rename_iff p policy value).mpr isPending)
  | boundaryReturned => exact .boundaryReturned
  | boundaryBatchNil => exact .boundaryBatchNil
  | boundaryBatchCons => exact .boundaryBatchCons
  | @boundaryNativeEmittedRaw _ _ _ _ live scope caller original value activation stack =>
      simpa [Control.rename, Task.rename, Completed.Boundary.rename,
        Entry.Value.rename_erase] using
        (LocalStep.boundaryNativeEmittedRaw (live := live.map (renameTypeVars p))
          (scope := scope.map p) (caller := caller.map (renameTypeVars p))
          (original := original.rename p) (value := value.rename p)
          (activation := activation.rename p) (stack := stack.map (Continuation.rename p)))
  | @boundaryNativeEmittedReturn _ _ _ _ live scope caller original expected value activation stack =>
      simpa [Control.rename, Task.rename, Continuation.rename, Completed.Boundary.rename,
        Entry.Value.rename_erase] using
        (LocalStep.boundaryNativeEmittedReturn (live := live.map (renameTypeVars p))
          (scope := scope.map p) (caller := caller.map (renameTypeVars p))
          (original := original.rename p) (expected := renameTypeVars p expected)
          (value := value.rename p) (activation := activation.rename p)
          (stack := stack.map (Continuation.rename p)))
  | boundaryNativeCompletedRaw =>
      simpa [Control.rename, Task.rename, Completed.Boundary.rename,
        Completed.Result.rename] using
        LocalStep.boundaryNativeCompletedRaw
  | @boundaryNativeCompletedReturn space _ lookup policy live scope caller original expected
      value activation results stack returned =>
      have returnedRenamed :
          Completed.NativeCompletedReturnRel (Spec.Eval.Renaming.space p space)
            (Completed.renameCastLookup p lookup
              (invocationTypeScope (scope.map p) (live.map (renameTypeVars p))
                (original.rename p).erase (renameTypeVars p expected) (activation.rename p).bindings)
              (Spec.Eval.Renaming.space p space))
            policy (value.rename p) (renameTypeVars p expected)
            (activation.rename p) (results.map (Completed.Result.rename p)) := by
        simpa only [Entry.Value.rename_erase, Completed.Frame.rename_bindings,
          Spec.Eval.Renaming.invocation_scope, Completed.renameCastLookup_apply] using
          returned.rename p
      exact LocalStep.boundaryNativeCompletedReturn returnedRenamed
  | @publish _ _ _ policy original raw selected stack priority =>
      have priorityRenamed :
          SuccessPriorityRel (fun item : Completed.Result => isErrorAtom item.1.erase)
            ((raw.map (Completed.Result.rename p)).map (Completed.readResult policy))
            (selected.map (Completed.Result.rename p)) := by
        have mapped := Completed.SuccessPriorityRel.rename_results p priority
        have readMap :
            (raw.map (Completed.readResult policy)).map (Completed.Result.rename p) =
              (raw.map (Completed.Result.rename p)).map (Completed.readResult policy) := by
          simp [List.map_map, Function.comp_def]
        rwa [readMap] at mapped
      simpa [Control.rename, Continuation.rename, List.map_map, Function.comp_def] using
        LocalStep.publish (original := renameTypeVars p original) priorityRenamed
  | @singleton _ _ _ _ results stack =>
      simpa [Control.rename, Continuation.rename, List.map_map, Function.comp_def] using
        (LocalStep.singleton (results := results.map (Completed.Result.rename p))
          (stack := stack.map (Continuation.rename p)))
  | branches => exact .branches
  | @tupleTail _ _ _ _ head results stack =>
      simpa [Control.rename, Continuation.rename, List.map_map, Function.comp_def] using
        (LocalStep.tupleTail (head := head.rename p)
          (results := results.map (Completed.Result.rename p))
          (stack := stack.map (Continuation.rename p)))
  | arguments => exact .arguments
  | @argumentTail _ _ _ _ head results stack =>
      simpa [Control.rename, Continuation.rename, List.map_map, Function.comp_def] using
        (LocalStep.argumentTail (head := head.rename p)
          (results := results.map (Completed.Result.rename p))
          (stack := stack.map (Continuation.rename p)))
  | functionHeads => exact .functionHeads
  | @functionAssemble _ _ _ _ head results stack =>
      simpa [Control.rename, Continuation.rename, List.map_map, Function.comp_def] using
        (LocalStep.functionAssemble (head := head.rename p)
          (results := results.map (Completed.Result.rename p))
          (stack := stack.map (Continuation.rename p)))
  | @diagnostics _ _ _ _ errors activation results stack =>
      simpa [Control.rename, Continuation.rename, List.map_append,
        Completed.diagnosticResults_rename] using
        (LocalStep.diagnostics (errors := errors.map (renameTypeVars p))
          (activation := activation.rename p)
          (results := results.map (Completed.Result.rename p))
          (stack := stack.map (Continuation.rename p)))
  | boundaryBatch => exact .boundaryBatch
  | calls => exact .calls
  | append => exact .append
  | prepend =>
      simpa [Control.rename, Continuation.rename, List.map_append] using LocalStep.prepend
  | contextStep _ ih => exact .contextStep ih
  | contextReturn => exact .contextReturn

theorem LocalStep.rename_iff (p : Equiv.Perm String)
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {lookup : Completed.CastLookup} {policy : Completed.Policy}
    {before after : Control × List Continuation} :
    LocalStep (Spec.Eval.Renaming.space p space) (Spec.Eval.Renaming.dispatch p dispatch)
      (Completed.renameCastLookup p lookup) policy
      (before.1.rename p, before.2.map (Continuation.rename p))
      (after.1.rename p, after.2.map (Continuation.rename p)) ↔
      LocalStep space dispatch lookup policy before after := by
  constructor
  · intro renamed
    have back := renamed.rename p.symm
    rw [Spec.Eval.Renaming.space_inverse] at back
    rcases before with ⟨bCtrl, bStack⟩
    rcases after with ⟨aCtrl, aStack⟩
    simpa [List.map_map, Function.comp_def] using back
  · exact LocalStep.rename p

theorem LocalSteps.rename (p : Equiv.Perm String)
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {lookup : Completed.CastLookup} {policy : Completed.Policy}
    {before after : Control × List Continuation}
    (path : LocalSteps space dispatch lookup policy before after) :
    LocalSteps (Spec.Eval.Renaming.space p space) (Spec.Eval.Renaming.dispatch p dispatch)
      (Completed.renameCastLookup p lookup) policy
      (before.1.rename p, before.2.map (Continuation.rename p))
      (after.1.rename p, after.2.map (Continuation.rename p)) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.rename p)

theorem LocalSteps.rename_iff (p : Equiv.Perm String)
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {lookup : Completed.CastLookup} {policy : Completed.Policy}
    {before after : Control × List Continuation} :
    LocalSteps (Spec.Eval.Renaming.space p space) (Spec.Eval.Renaming.dispatch p dispatch)
      (Completed.renameCastLookup p lookup) policy
      (before.1.rename p, before.2.map (Continuation.rename p))
      (after.1.rename p, after.2.map (Continuation.rename p)) ↔
      LocalSteps space dispatch lookup policy before after := by
  constructor
  · intro renamed
    have back := renamed.rename p.symm
    rw [Spec.Eval.Renaming.space_inverse] at back
    rcases before with ⟨bCtrl, bStack⟩
    rcases after with ⟨aCtrl, aStack⟩
    simpa [List.map_map, Function.comp_def] using back
  · exact LocalSteps.rename p

theorem Step.rename (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Completed.Policy} {before after : Configuration}
    (step : Step dispatch lookup policy before after) :
    Step (Spec.Eval.Renaming.dispatch p dispatch) (Completed.renameCastLookup p lookup)
      policy (before.rename p) (after.rename p) := by
  cases step with
  | internal localStep =>
      exact .internal (localStep.rename p)
  | publish =>
      simpa [Configuration.rename, Control.rename, List.map_append] using Step.publish

theorem Step.rename_iff (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Completed.Policy} {before after : Configuration} :
    Step (Spec.Eval.Renaming.dispatch p dispatch) (Completed.renameCastLookup p lookup)
      policy (before.rename p) (after.rename p) ↔
      Step dispatch lookup policy before after := by
  constructor
  · intro renamed
    simpa using renamed.rename p.symm
  · exact Step.rename p

theorem Steps.rename (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Completed.Policy} {before after : Configuration}
    (path : Steps dispatch lookup policy before after) :
    Steps (Spec.Eval.Renaming.dispatch p dispatch) (Completed.renameCastLookup p lookup)
      policy (before.rename p) (after.rename p) := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (step.rename p)

theorem Steps.rename_iff (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup}
    {policy : Completed.Policy} {before after : Configuration} :
    Steps (Spec.Eval.Renaming.dispatch p dispatch) (Completed.renameCastLookup p lookup)
      policy (before.rename p) (after.rename p) ↔
      Steps dispatch lookup policy before after := by
  constructor
  · intro renamed
    simpa using renamed.rename p.symm
  · exact Steps.rename p

/-! ### Specializations to `rawLookup` and `scopedLookup` -/

theorem LocalStep.rename_rawLookup (p : Equiv.Perm String)
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
    {before after : Control × List Continuation}
    (step : LocalStep space dispatch Completed.rawLookup policy before after) :
    LocalStep (Spec.Eval.Renaming.space p space) (Spec.Eval.Renaming.dispatch p dispatch)
      Completed.rawLookup policy
      (before.1.rename p, before.2.map (Continuation.rename p))
      (after.1.rename p, after.2.map (Continuation.rename p)) := by
  simpa only [Completed.renameCastLookup_rawLookup] using step.rename p

theorem LocalStep.rename_scopedLookup (p : Equiv.Perm String)
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
    {before after : Control × List Continuation}
    (step : LocalStep space dispatch Completed.scopedLookup policy before after) :
    LocalStep (Spec.Eval.Renaming.space p space) (Spec.Eval.Renaming.dispatch p dispatch)
      Completed.scopedLookup policy
      (before.1.rename p, before.2.map (Continuation.rename p))
      (after.1.rename p, after.2.map (Continuation.rename p)) := by
  simpa only [Completed.renameCastLookup_scopedLookup] using step.rename p

theorem Step.rename_rawLookup (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
    {before after : Configuration}
    (step : Step dispatch Completed.rawLookup policy before after) :
    Step (Spec.Eval.Renaming.dispatch p dispatch) Completed.rawLookup
      policy (before.rename p) (after.rename p) := by
  simpa only [Completed.renameCastLookup_rawLookup] using step.rename p

theorem Step.rename_scopedLookup (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
    {before after : Configuration}
    (step : Step dispatch Completed.scopedLookup policy before after) :
    Step (Spec.Eval.Renaming.dispatch p dispatch) Completed.scopedLookup
      policy (before.rename p) (after.rename p) := by
  simpa only [Completed.renameCastLookup_scopedLookup] using step.rename p

theorem Steps.rename_rawLookup (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
    {before after : Configuration}
    (path : Steps dispatch Completed.rawLookup policy before after) :
    Steps (Spec.Eval.Renaming.dispatch p dispatch) Completed.rawLookup
      policy (before.rename p) (after.rename p) := by
  simpa only [Completed.renameCastLookup_rawLookup] using path.rename p

theorem Steps.rename_scopedLookup (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
    {before after : Configuration}
    (path : Steps dispatch Completed.scopedLookup policy before after) :
    Steps (Spec.Eval.Renaming.dispatch p dispatch) Completed.scopedLookup
      policy (before.rename p) (after.rename p) := by
  simpa only [Completed.renameCastLookup_scopedLookup] using path.rename p

/-! ### Resumption at a Saved Continuation and Public-Scope Observation Preservation -/

theorem resumption_transport (p : Equiv.Perm String)
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Completed.Policy}
    {initial paused completed : Configuration} {answers : List Completed.Result}
    (prefixPath : Steps dispatch lookup policy initial paused)
    (resumePath : Steps dispatch lookup policy paused completed)
    (done : observe completed = some answers) :
    Steps (Spec.Eval.Renaming.dispatch p dispatch) (Completed.renameCastLookup p lookup) policy
      (initial.rename p) (paused.rename p) ∧
    Steps (Spec.Eval.Renaming.dispatch p dispatch) (Completed.renameCastLookup p lookup) policy
      (paused.rename p) (completed.rename p) ∧
    observe (completed.rename p) = some (answers.map (Completed.Result.rename p)) :=
  ⟨prefixPath.rename p, resumePath.rename p, (observe_rename_some_iff p completed answers).mpr done⟩

theorem result_public_scope_preserved (publicScope : List String)
    (p : Equiv.Perm String) (fixed : ∀ name ∈ publicScope, p name = name)
    (result : Completed.Result) :
    (Completed.Result.rename p result).1 = Entry.Value.rename p result.1 ∧
    (Completed.Result.rename p result).2 = result.2.rename p ∧
    BindingTheoryEquivAt publicScope
      result.2.bindings (Completed.Result.rename p result).2.bindings :=
  ⟨rfl, rfl,
    BindingTheoryEquivAt.of_renameBindings publicScope result.2.bindings p fixed⟩

theorem results_public_scope_preserved (publicScope : List String)
    (p : Equiv.Perm String) (fixed : ∀ name ∈ publicScope, p name = name)
    (answers : List Completed.Result) :
    List.Forall₂ (fun original renamed =>
      renamed.1 = Entry.Value.rename p original.1 ∧
      renamed.2 = original.2.rename p ∧
      BindingTheoryEquivAt publicScope original.2.bindings renamed.2.bindings)
      answers (answers.map (Completed.Result.rename p)) := by
  induction answers with
  | nil => exact .nil
  | cons item rest ih =>
      exact .cons (result_public_scope_preserved publicScope p fixed item) ih

theorem observed_public_scope_preserved (publicScope : List String)
    (p : Equiv.Perm String) (fixed : ∀ name ∈ publicScope, p name = name)
    {dispatch : Spec.Eval.GroundedDispatch} {lookup : Completed.CastLookup} {policy : Completed.Policy}
    {before after : Configuration} {answers : List Completed.Result}
    (path : Steps dispatch lookup policy before after)
    (done : observe after = some answers) :
    Steps (Spec.Eval.Renaming.dispatch p dispatch) (Completed.renameCastLookup p lookup) policy
      (before.rename p) (after.rename p) ∧
    observe (after.rename p) = some (answers.map (Completed.Result.rename p)) ∧
    List.Forall₂ (fun original renamed =>
      renamed.1 = Entry.Value.rename p original.1 ∧
      renamed.2 = original.2.rename p ∧
      BindingTheoryEquivAt publicScope original.2.bindings renamed.2.bindings)
      answers (answers.map (Completed.Result.rename p)) :=
  ⟨path.rename p,
   (observe_rename_some_iff p after answers).mpr done,
   results_public_scope_preserved publicScope p fixed answers⟩

/-! ### Kernel-Checked Contextual Machine Controls -/

namespace RenamingControls

open Spec.Eval.Completed.Controls

/-- Permutation swapping the private alias target `"y"` with `"z"` while fixing
the public variable `"x"`. -/
def swapPrivateYZ : Equiv.Perm String := Equiv.swap "y" "z"

theorem swapPrivateYZ_fixes_public : ∀ name ∈ ["x"], swapPrivateYZ name = name := by
  intro name member
  obtain rfl := List.mem_singleton.mp member
  decide +kernel

/-- Control 1: Open binding-changing computation with an alias-bearing incoming
frame (`x -> $y`), a nonempty saved continuation (`[.singleton]`), and an
existing emitted occurrence (`[(Entry.Value.symbol "prior", argumentAliasFrame)]`). -/
def priorEmitted : List Completed.Result :=
  [(Entry.Value.symbol "prior", argumentAliasFrame)]

def openInitial : Configuration :=
  ⟨argumentTypeSpace,
   .work (.tuple [] ["x"] [Entry.Value.symbol "datum"] argumentAliasFrame),
   [.singleton],
   priorEmitted⟩

def openPaused : Configuration :=
  ⟨argumentTypeSpace,
   .work (.atom [] ["x"] (Entry.Value.symbol "datum") (.var "y") argumentAliasFrame),
   [.singleton, .singleton],
   priorEmitted⟩

def openAfterCast : Configuration :=
  ⟨argumentTypeSpace,
   .returning [(Entry.Value.symbol "datum", argumentCastFrame)],
   [.singleton, .singleton],
   priorEmitted⟩

def openAfterFirstSingleton : Configuration :=
  ⟨argumentTypeSpace,
   .returning [(Entry.Value.expression .active [Entry.Value.symbol "datum"], argumentCastFrame)],
   [.singleton],
   priorEmitted⟩

def openAfterSecondSingleton : Configuration :=
  ⟨argumentTypeSpace,
   .returning [(Entry.Value.expression .active [Entry.Value.expression .active [Entry.Value.symbol "datum"]],
     argumentCastFrame)],
   [],
   priorEmitted⟩

def openCompleted : Configuration :=
  ⟨argumentTypeSpace,
   .returning [],
   [],
   priorEmitted ++ [(Entry.Value.expression .active [Entry.Value.expression .active [Entry.Value.symbol "datum"]],
     argumentCastFrame)]⟩

theorem open_cast_localStep_of_query (dispatch : Spec.Eval.GroundedDispatch) (policy : Completed.Policy)
    (lookup : Completed.CastLookup)
    (queried : lookup (invocationTypeScope ["x"] [] (.symbol "datum") (.var "y") argumentAliasFrame.bindings)
      argumentTypeSpace argumentAliasFrame.bindings (.symbol "datum") (.var "y") [.symbol "T"]) :
    LocalStep argumentTypeSpace dispatch lookup policy
      (.work (.atom [] ["x"] (Entry.Value.symbol "datum") (.var "y") argumentAliasFrame),
       [.singleton, .singleton])
      (.returning [(Entry.Value.symbol "datum", argumentCastFrame)],
       [.singleton, .singleton]) := by
  have matched : policy.matching.Rel (.var "y") (.symbol "T")
      argumentAliasFrame.bindings argumentCastFrame.bindings := by
    cases policy.matching with
    | raw => exact argument_cast_match
    | finite => exact ⟨argument_cast_match, argument_cast_certificate.satisfiable⟩
  have read : argumentAliasFrame.read policy (.symbol "datum") = .symbol "datum" := by
    simp [Completed.Frame.read, Entry.Value.substitute]
  have renewed : Completed.Frame.CastRenewRel policy (lookup (invocationTypeScope ["x"] [] (.symbol "datum") (.var "y") argumentAliasFrame.bindings) argumentTypeSpace)
      (.symbol "datum") (.var "y") argumentAliasFrame argumentCastFrame :=
    .matched (earlier := []) (later := []) queried rfl (by simp) matched
      (by simpa only [Entry.Value.ofAtom, argumentCastFrame] using
        argument_cast_unification policy.rebuilding)
  apply LocalStep.cast (raw := [(.symbol "datum", argumentCastFrame.bindings)])
  · simpa only [read, Entry.Value.erase, Entry.Value.status] using
      (Entry.Rel.cast (policy := policy.reentry) (status := .active)
        (expected := .var "y")
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (.symbol "datum") (by decide)
        (Or.inl ⟨"datum", rfl⟩) (by intro impossible; cases impossible))
  · simp only [Completed.Frame.read, Entry.Value.substitute, Entry.Value.erase]
    exact .success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) matched
  · simp only [read]
    refine .cons ⟨?_, ?_, ?_⟩ .nil
    · simp [Completed.rawResult, Entry.Value.erase]
    · simpa only [Entry.Value.erase] using renewed
    · simp [Entry.Value.erase]

/-- The historical storage traversal is one client of the query-parametric control. -/
theorem open_cast_localStep (dispatch : Spec.Eval.GroundedDispatch) (policy : Completed.Policy) :
    LocalStep argumentTypeSpace dispatch Completed.rawLookup policy
      (.work (.atom [] ["x"] (Entry.Value.symbol "datum") (.var "y") argumentAliasFrame),
       [.singleton, .singleton])
      (.returning [(Entry.Value.symbol "datum", argumentCastFrame)],
       [.singleton, .singleton]) :=
  open_cast_localStep_of_query dispatch policy Completed.rawLookup
    (StorageTypesRel.symbolKnown (.hit .nil) (by decide))

/-- An actual open cast with saved callers runs under a different coherent
complete enumeration policy. Its reached alias frame and both saved
continuations remain the same. The policies are not pooled into one run. -/
theorem open_cast_complete_enumeration (dispatch : Spec.Eval.GroundedDispatch) (policy : Completed.Policy) :
    LocalStep argumentTypeSpace dispatch (Completed.literalEnumerationLookup
      (TypeEnumeration.storage.reorder List.reverse List.reverse_perm)) policy
      (.work (.atom [] ["x"] (Entry.Value.symbol "datum") (.var "y") argumentAliasFrame),
       [.singleton, .singleton])
      (.returning [(Entry.Value.symbol "datum", argumentCastFrame)],
       [.singleton, .singleton]) :=
  open_cast_localStep_of_query dispatch policy (Completed.literalEnumerationLookup
      (TypeEnumeration.storage.reorder List.reverse List.reverse_perm))
    ⟨_, StorageTypesRel.symbolKnown (.hit .nil) (by decide), rfl⟩

theorem open_resumption_steps (dispatch : Spec.Eval.GroundedDispatch) (policy : Completed.Policy) :
    Steps dispatch Completed.rawLookup policy openPaused openCompleted := by
  have step1 : Step dispatch Completed.rawLookup policy openPaused openAfterCast :=
    .internal (open_cast_localStep dispatch policy)
  have step2 : Step dispatch Completed.rawLookup policy openAfterCast openAfterFirstSingleton := by
    simpa [openAfterCast, openAfterFirstSingleton, Completed.tupleSingleton,
      Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      (Step.internal (space := argumentTypeSpace) (dispatch := dispatch)
        (lookup := Completed.rawLookup) (policy := policy)
        (emitted := priorEmitted)
        (LocalStep.singleton (results := [(Entry.Value.symbol "datum", argumentCastFrame)])
          (stack := [.singleton])))
  have step3 : Step dispatch Completed.rawLookup policy
      openAfterFirstSingleton openAfterSecondSingleton := by
    simpa [openAfterFirstSingleton, openAfterSecondSingleton, Completed.tupleSingleton,
      Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      (Step.internal (space := argumentTypeSpace) (dispatch := dispatch)
        (lookup := Completed.rawLookup) (policy := policy)
        (emitted := priorEmitted)
        (LocalStep.singleton
          (results := [(Entry.Value.expression .active [Entry.Value.symbol "datum"], argumentCastFrame)])
          (stack := [])))
  have step4 : Step dispatch Completed.rawLookup policy openAfterSecondSingleton openCompleted :=
    Step.publish
  exact (((Relation.ReflTransGen.single step1).tail step2).tail step3).tail step4

/-- Control 1 theorem: Consistent renaming transports the paused open computation,
its nonempty continuation, its prior emitted occurrence, and its changed
certified frame through resumption, while preserving public binding observations
on `["x"]` and updating the public variable `"x"` to `.symbol "T"`. -/
theorem control1_open_resumption_and_public_observation
    (dispatch : Spec.Eval.GroundedDispatch) (policy : Completed.Policy) :
    Steps (Spec.Eval.Renaming.dispatch swapPrivateYZ dispatch) Completed.rawLookup policy
      (openPaused.rename swapPrivateYZ) (openCompleted.rename swapPrivateYZ) ∧
    observe (openCompleted.rename swapPrivateYZ) =
      some ((priorEmitted ++
        [(Entry.Value.expression .active [Entry.Value.expression .active [Entry.Value.symbol "datum"]],
          argumentCastFrame)]).map (Completed.Result.rename swapPrivateYZ)) ∧
    BindingTheoryEquivAt ["x"] argumentCastFrame.bindings
      (argumentCastFrame.rename swapPrivateYZ).bindings ∧
    (argumentCastFrame.rename swapPrivateYZ).read policy (.var "x") = .symbol "T" := by
  refine ⟨(open_resumption_steps dispatch policy).rename_rawLookup swapPrivateYZ, ?_, ?_, ?_⟩
  · exact (observe_rename_some_iff swapPrivateYZ openCompleted _).mpr rfl
  · exact BindingTheoryEquivAt.of_renameBindings ["x"] argumentCastFrame.bindings
      swapPrivateYZ swapPrivateYZ_fixes_public
  · have readX := (argument_cast_changes_readout policy).2
    have renamedRead := Completed.Frame.read_rename swapPrivateYZ policy argumentCastFrame (.var "x")
    have fixedX : Entry.Value.rename swapPrivateYZ (.var "x") = .var "x" := by
      rw [Entry.Value.rename_var]
      rfl
    have fixedT : Entry.Value.rename swapPrivateYZ (.symbol "T") = .symbol "T" :=
      Entry.Value.rename_symbol swapPrivateYZ "T"
    rw [fixedX, readX, fixedT] at renamedRead
    exact renamedRead

/-- Control 2: Typed transition preserving repeated positions in a signature
(`rawSignature : (-> Atom Atom)` with repeated `Atom` positions and duplicated
declared argument types `[D, D]`) together with changed certified frame casts. -/
theorem control2_typed_selection_and_changed_frame_transport
    (dispatch : Spec.Eval.GroundedDispatch) (policy : Completed.Policy) :
    LocalStep (Spec.Eval.Renaming.space swapPrivateYZ typedInvocationSpace)
      (Spec.Eval.Renaming.dispatch swapPrivateYZ dispatch)
      Completed.rawLookup policy
      ((Control.work (.atom [] ["x"] typedInvocation Atom.undefinedType Completed.Frame.empty)).rename swapPrivateYZ,
       [])
      ((Control.work (.invocations [] ["x"] Atom.undefinedType rawSignature
          (.symbol "hold") [.symbol "datum"] [Completed.Frame.empty, Completed.Frame.empty])).rename swapPrivateYZ,
       [Continuation.rename swapPrivateYZ (.publish typedInvocation.erase)]) ∧
    LocalStep (Spec.Eval.Renaming.space swapPrivateYZ argumentTypeSpace)
      (Spec.Eval.Renaming.dispatch swapPrivateYZ dispatch)
      Completed.rawLookup policy
      ((Control.work (.atom [] ["x"] (.symbol "datum") (.var "y") argumentAliasFrame)).rename swapPrivateYZ,
       ([.singleton, .singleton] : List Continuation).map (Continuation.rename swapPrivateYZ))
      ((Control.returning [(.symbol "datum", argumentCastFrame)]).rename swapPrivateYZ,
       ([.singleton, .singleton] : List Continuation).map (Continuation.rename swapPrivateYZ)) := by
  have entered : Entry.Rel policy.reentry
      (Completed.Frame.empty.read policy typedInvocation).status
      (Completed.Frame.empty.read policy typedInvocation).erase
      Atom.undefinedType .interpret := by
    simpa only [Completed.Frame.read_empty, typedInvocation, Entry.Value.status,
      Entry.Value.erase, List.map_cons, List.map_nil] using
      (Entry.Rel.expression (policy := policy.reentry) (status := .active)
        (head := .symbol "hold") (tail := [.symbol "datum"]) (expected := Atom.undefinedType)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
  have selectionStep :
      LocalStep typedInvocationSpace dispatch Completed.rawLookup policy
        (.work (.atom [] ["x"] typedInvocation Atom.undefinedType Completed.Frame.empty), [])
        (.work (.invocations [] ["x"] Atom.undefinedType rawSignature
          (.symbol "hold") [.symbol "datum"] [Completed.Frame.empty, Completed.Frame.empty]),
         [.publish typedInvocation.erase]) := by
    simpa only [Completed.Frame.read_empty] using
      LocalStep.atomFunction (value := typedInvocation) entered (Completed.Frame.read_empty _ _)
        (by simpa only [Completed.Frame.read_empty, Entry.Value.erase] using
          typed_invocation_selection policy [] ["x"])
  exact ⟨selectionStep.rename_rawLookup swapPrivateYZ,
    (open_cast_localStep dispatch policy).rename_rawLookup swapPrivateYZ⟩

/-- Polymorphic arrow type `(-> $t $t)` with an actual repeated type variable `$t`,
together with two fresh instances `(-> $y $y)` and `(-> $w $w)` whose private
variables remain distinct. -/
def polyArrow : Atom := .expression [.symbol "->", .var "t", .var "t"]

def polySigY : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", .var "y", .var "y"], [.var "y"], .var "y", rfl⟩

def polySigW : SelectedTypePolicy :=
  ⟨.expression [.symbol "->", .var "w", .var "w"], [.var "w"], .var "w", rfl⟩

def polyArrowSpace : Space :=
  ⟨[.expression [.symbol ":", .symbol "hold", polySigY.functionType],
    .expression [.symbol ":", .symbol "hold", polySigW.functionType],
    .expression [.symbol ":", .symbol "datum", .symbol "T"]]⟩

theorem polyArrow_fresh_instances :
    renameTypeVars (Equiv.swap "t" "y") polyArrow = polySigY.functionType ∧
    renameTypeVars (Equiv.swap "t" "w") polyArrow = polySigW.functionType ∧
    polySigY.functionType ≠ polySigW.functionType := by
  refine ⟨?_, ?_, by decide⟩
  · simp [polyArrow, polySigY, Equiv.swap_apply_left]
  · simp [polyArrow, polySigW, Equiv.swap_apply_left]

theorem polyArrow_operator_query :
    StorageTypesRel polyArrowSpace (.symbol "hold")
      [polySigY.functionType, polySigW.functionType] := by
  apply StorageTypesRel.symbolKnown
  · exact .hit (.hit (.skip (by intro type; simp) .nil))
  · simp

theorem polyArrow_argument_query :
    StorageTypesRel polyArrowSpace (.symbol "datum") [.symbol "T"] := by
  apply StorageTypesRel.symbolKnown
  · exact .skip (by intro type; simp) (.skip (by intro type; simp) (.hit .nil))
  · simp

theorem polyArrow_applicability (policy : Completed.Policy) :
    Completed.ApplicationChecksRel polyArrowSpace (rawTypeLookupRel polyArrowSpace) policy
      typedInvocation.erase Atom.undefinedType polySigY argumentAliasFrame [argumentCastFrame] [] := by
  have matchedArg : policy.matching.Rel (.var "y") (.symbol "T")
      argumentAliasFrame.bindings argumentCastFrame.bindings := by
    cases selected : policy.matching with
    | raw => exact argument_cast_match
    | finite => exact ⟨argument_cast_match, argument_cast_certificate.satisfiable⟩
  have acceptedArg : Completed.TypeCheckRel policy (.var "y") argumentAliasFrame
      (.symbol "T") (.inr argumentCastFrame) :=
    .accepted (.unified matchedArg
      (by simpa only [Entry.Value.ofAtom, argumentCastFrame] using
        argument_cast_unification policy.rebuilding))
  have checkedArg : Completed.ArgumentChecksRel polyArrowSpace (rawTypeLookupRel polyArrowSpace) policy
      typedInvocation.erase (.symbol "datum") (.var "y") 1
      [argumentAliasFrame] [argumentCastFrame] [] := by
    simpa [Completed.checkedFrames, Completed.checkedFailures] using
      (Completed.ArgumentChecksRel.cons (expression := typedInvocation.erase) (position := 1)
        polyArrow_argument_query (.cons acceptedArg .nil) .nil)
  have matchedRet : policy.matching.Rel Atom.undefinedType (.var "y")
      argumentCastFrame.bindings argumentCastFrame.bindings := by
    cases selected : policy.matching with
    | raw => exact .undefinedLeft _ _
    | finite => exact ⟨.undefinedLeft _ _, argumentCastFrame.certified.satisfiable⟩
  have returned : Completed.TypeCheckRel policy Atom.undefinedType argumentCastFrame
      (.var "y") (.inr argumentCastFrame) :=
    .accepted (.unchanged matchedRet)
  simpa [Completed.checkedFrames, Completed.checkedFailures] using
    (Completed.ApplicationChecksRel.checked (selected := polySigY) (expected := Atom.undefinedType)
      (before := argumentAliasFrame)
      (show typedInvocation.erase = .expression [.symbol "hold", .symbol "datum"] by
        simp [typedInvocation, Entry.Value.erase])
      (.cons checkedArg .nil) (.cons returned .nil))

theorem polyArrow_selection (policy : Completed.Policy) (live : List Atom) (scope : List String) :
    Completed.InvocationSelectionRel polyArrowSpace Completed.rawLookup policy live scope
      typedInvocation.erase (.symbol "hold") Atom.undefinedType argumentAliasFrame
      (.selected polySigY [argumentCastFrame]) :=
  ⟨[polySigY.functionType, polySigW.functionType], polyArrow_operator_query,
    .selected (polyArrow_applicability policy) (by simp)⟩

/-- Control 2b: Machine-level repeated-type-variable control on `(-> $t $t)` with
two fresh instances `(-> $y $y)` and `(-> $w $w)`. One simultaneous permutation
(`swapPrivateYZ`) keeps both occurrences of the first instance's variable connected,
does not merge the two distinct instances' variables, and preserves the reached
frame/readout correlation through the executed selection transition. -/
theorem control2b_polymorphic_arrow_correlation_and_fresh_instances
    (dispatch : Spec.Eval.GroundedDispatch) (policy : Completed.Policy) :
    LocalStep (Spec.Eval.Renaming.space swapPrivateYZ polyArrowSpace)
      (Spec.Eval.Renaming.dispatch swapPrivateYZ dispatch)
      Completed.rawLookup policy
      ((Control.work (.atom [] ["x"] typedInvocation Atom.undefinedType argumentAliasFrame)).rename swapPrivateYZ,
       [])
      ((Control.work (.invocations [] ["x"] Atom.undefinedType polySigY
          (.symbol "hold") [.symbol "datum"] [argumentCastFrame])).rename swapPrivateYZ,
       [Continuation.rename swapPrivateYZ (.publish typedInvocation.erase)]) ∧
    (Spec.Eval.Renaming.policy swapPrivateYZ polySigY).argumentTypes =
      [(Spec.Eval.Renaming.policy swapPrivateYZ polySigY).returnType] ∧
    (Spec.Eval.Renaming.policy swapPrivateYZ polySigY).returnType ≠
      (Spec.Eval.Renaming.policy swapPrivateYZ polySigW).returnType ∧
    (argumentCastFrame.rename swapPrivateYZ).read policy
      (Entry.Value.ofAtom (Spec.Eval.Renaming.policy swapPrivateYZ polySigY).returnType) = .symbol "T" ∧
    (argumentCastFrame.rename swapPrivateYZ).read policy (.var "x") = .symbol "T" ∧
    (argumentCastFrame.rename swapPrivateYZ).read policy
      (Entry.Value.ofAtom (Spec.Eval.Renaming.policy swapPrivateYZ polySigW).returnType) = .var "w" := by
  have readInv : argumentAliasFrame.read policy typedInvocation = typedInvocation := by
    simp [Completed.Frame.read, typedInvocation, Entry.Value.substitute, Entry.Value.rebuildStatus]
    cases policy.rebuilding <;> rfl
  have entered : Entry.Rel policy.reentry
      (argumentAliasFrame.read policy typedInvocation).status
      (argumentAliasFrame.read policy typedInvocation).erase
      Atom.undefinedType .interpret := by
    rw [readInv]
    simpa only [typedInvocation, Entry.Value.status,
      Entry.Value.erase, List.map_cons, List.map_nil] using
      (Entry.Rel.expression (policy := policy.reentry) (status := .active)
        (head := .symbol "hold") (tail := [.symbol "datum"]) (expected := Atom.undefinedType)
        (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
  have selectionStep :
      LocalStep polyArrowSpace dispatch Completed.rawLookup policy
        (.work (.atom [] ["x"] typedInvocation Atom.undefinedType argumentAliasFrame), [])
        (.work (.invocations [] ["x"] Atom.undefinedType polySigY
          (.symbol "hold") [.symbol "datum"] [argumentCastFrame]),
         [.publish typedInvocation.erase]) := by
    simpa only [readInv] using
      LocalStep.atomFunction (value := typedInvocation) entered readInv
        (by
          rw [readInv]
          simpa only [Entry.Value.erase] using polyArrow_selection policy [] ["x"])
  refine ⟨selectionStep.rename_rawLookup swapPrivateYZ, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Spec.Eval.Renaming.policy, polySigY]
  · have hYZ : swapPrivateYZ "y" = "z" := Equiv.swap_apply_left "y" "z"
    have hWZ : swapPrivateYZ "w" = "w" :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    simp [Spec.Eval.Renaming.policy, polySigY, polySigW, hYZ, hWZ]
  · have readY : argumentCastFrame.read policy (.var "y") = .symbol "T" := by
      simp [Completed.Frame.read, Entry.Value.substitute, Entry.Value.resolve,
        argumentCastFrame, argumentCastEnvironment, List.lookup]
    have renamedRead :=
      Completed.Frame.read_rename swapPrivateYZ policy argumentCastFrame (.var "y")
    simp only [Spec.Eval.Renaming.policy, polySigY, renameTypeVars, Entry.Value.ofAtom,
      Entry.Value.rename_var, readY, Entry.Value.rename_symbol] at renamedRead ⊢
    exact renamedRead
  · exact (control1_open_resumption_and_public_observation dispatch policy).2.2.2
  · have readW : argumentCastFrame.read policy (.var "w") = .var "w" := by
      simp [Completed.Frame.read, Entry.Value.substitute, Entry.Value.resolve,
        argumentCastFrame, argumentCastEnvironment, List.lookup]
    have hWZ : swapPrivateYZ "w" = "w" :=
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have renamedRead :=
      Completed.Frame.read_rename swapPrivateYZ policy argumentCastFrame (.var "w")
    simp only [Spec.Eval.Renaming.policy, polySigW, renameTypeVars, Entry.Value.ofAtom,
      Entry.Value.rename_var, readW, hWZ] at renamedRead ⊢
    exact renamedRead

/-- Control 3 (Negative): Partial renaming that renames only the current syntax
(`.var "x" ↦ .var "z"`) while retaining the unrenamed environment (`x ↦ T`) or
continuation changes the reached answer (`$z` instead of `T`), demonstrating
why the entire retained configuration must be renamed simultaneously. -/
def swapXZ : Equiv.Perm String := Equiv.swap "x" "z"

theorem control3_partial_renaming_changes_answer
    (space : Space) (dispatch : Spec.Eval.GroundedDispatch)
    (lookup : Completed.CastLookup) (policy : Completed.Policy) :
    LocalStep space dispatch lookup policy
      (.work (.atom [] [] (.var "x") Atom.atomType argumentCastFrame), [])
      (.returning [(.symbol "T", argumentCastFrame)], []) ∧
    LocalStep space dispatch lookup policy
      (.work (.atom [] [] (Entry.Value.rename swapXZ (.var "x")) Atom.atomType argumentCastFrame), [])
      (.returning [(.var "z", argumentCastFrame)], []) ∧
    (Entry.Value.rename swapXZ (.symbol "T") ≠ .var "z") := by
  have readX : argumentCastFrame.read policy (.var "x") = .symbol "T" :=
    (argument_cast_changes_readout policy).2
  have readZ : argumentCastFrame.read policy (Entry.Value.rename swapXZ (.var "x")) = .var "z" := by
    have swapped : Entry.Value.rename swapXZ (.var "x") = .var "z" := by
      simp [swapXZ]
    rw [swapped]
    simp [Completed.Frame.read, Entry.Value.substitute, Entry.Value.resolve,
      argumentCastFrame, argumentCastEnvironment, List.lookup]
  refine ⟨?_, ?_, by simp⟩
  · have step := LocalStep.delivered (admission := .historical) (space := space) (dispatch := dispatch)
      (lookup := lookup) (policy := policy) (live := []) (scope := [])
      (value := .var "x") (expected := Atom.atomType) (activation := argumentCastFrame)
      (stack := []) (Entry.atom_demand policy.reentry _ _)
    simpa only [readX] using step
  · have step := LocalStep.delivered (admission := .historical) (space := space) (dispatch := dispatch)
      (lookup := lookup) (policy := policy) (live := []) (scope := [])
      (value := Entry.Value.rename swapXZ (.var "x")) (expected := Atom.atomType)
      (activation := argumentCastFrame) (stack := [])
      (Entry.atom_demand policy.reentry _ _)
    simpa only [readZ] using step

/-- Control 4 (Diagnostic separation): Connect the diagnostic separation of
`Spec.Eval.Renaming.DiagnosticControls` to the machine transition
`LocalStep.minimalUnifyBadArity`: the transported dispatcher produces the
renamed source diagnostic, whereas the unchanged spelling-sensitive renderer
does not equal the renamed source diagnostic. -/
def diagnosticExchange : Equiv.Perm String := Equiv.swap "a" "b"

def badUnifySourceAtom : Atom :=
  .expression [.symbol "unify", .var "a", .symbol "A", .symbol "B"]

def badUnifyTargetAtom : Atom :=
  .expression [.symbol "unify", .var "b", .symbol "A", .symbol "B"]

def badUnifySourceValues : List Entry.Value :=
  [.var "a", .symbol "A", .symbol "B"]

def badUnifyTargetValues : List Entry.Value :=
  badUnifySourceValues.map (Entry.Value.rename diagnosticExchange)

theorem badUnifySourceAtom_renames :
    renameTypeVars diagnosticExchange badUnifySourceAtom = badUnifyTargetAtom := by
  simp [badUnifySourceAtom, badUnifyTargetAtom, diagnosticExchange]

theorem badUnify_rendered_text_not_equivariant :
    renameTypeVars diagnosticExchange (mkUnifyBadArityError badUnifySourceAtom) ≠
      mkUnifyBadArityError badUnifyTargetAtom := by
  change renameTypeVars diagnosticExchange
      (Atom.error badUnifySourceAtom (.symbol (unifyBadArityMessage badUnifySourceAtom))) ≠
    Atom.error badUnifyTargetAtom (.symbol (unifyBadArityMessage badUnifyTargetAtom))
  rw [Spec.Eval.Renaming.atom_error, badUnifySourceAtom_renames, Spec.Eval.Renaming.atom_symbol]
  decide +kernel

theorem control4_diagnostic_machine_separation
    (space : Space) (lookup : Completed.CastLookup) (policy : Completed.Policy) :
    LocalStep (Spec.Eval.Renaming.space diagnosticExchange space)
      (Spec.Eval.Renaming.dispatch diagnosticExchange
        ({ executable := fun _ => False, outcome := fun _ _ _ => False } : Spec.Eval.GroundedDispatch))
      (Completed.renameCastLookup diagnosticExchange lookup) policy
      (.work (.minimal [] [] none (.expression .active (.symbol "unify" :: badUnifyTargetValues))
        Completed.Frame.empty), [])
      (.returning [(Entry.Value.rename diagnosticExchange
        (Entry.Value.ofAtom (mkUnifyBadArityError badUnifySourceAtom)),
        Completed.Frame.empty)], []) ∧
    renameTypeVars diagnosticExchange
      (mkUnifyBadArityError badUnifySourceAtom) ≠
      mkUnifyBadArityError badUnifyTargetAtom := by
  let rawDispatch : Spec.Eval.GroundedDispatch :=
    { executable := fun _ => False, outcome := fun _ _ _ => False }
  have baseStep :
      LocalStep space rawDispatch lookup policy
        (.work (.minimal [] [] none (.expression .active (.symbol "unify" :: badUnifySourceValues))
          Completed.Frame.empty), [])
        (.returning [(Entry.Value.ofAtom
          (mkUnifyBadArityError badUnifySourceAtom),
          Completed.Frame.empty)], []) := by
    simpa [badUnifySourceValues, rawDispatch, mkUnifyBadArityError,
      badUnifySourceAtom, Entry.Value.erase] using
      (LocalStep.minimalUnifyBadArity (space := space) (dispatch := rawDispatch)
        (lookup := lookup) (policy := policy) (live := []) (scope := []) (caller := none)
        (readiness := .active) (tail := badUnifySourceValues)
        (activation := Completed.Frame.empty) (stack := []) (by decide))
  refine ⟨?_, badUnify_rendered_text_not_equivariant⟩
  simpa [Control.rename, Task.rename, Completed.Result.rename, badUnifyTargetValues] using
    baseStep.rename diagnosticExchange

end RenamingControls

end Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual
