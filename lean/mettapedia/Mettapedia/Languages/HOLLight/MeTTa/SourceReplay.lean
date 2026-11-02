import Mettapedia.Languages.HOLLight.MeTTa.ProofEvents

/-!
# Finite source-event paths execute the authored replay loop

The trace below records actual executions of `hol-light:step`, with their
complete source states. It retains event order and duplicate premise addresses.
The replay theorem executes the quoted `hol-light:run-from` equation itself.
It is an execution-composition law, not a logical soundness interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.SourceReplay

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State)

structure Command where
  key : Atom
  request : Atom
  deriving DecidableEq

def Command.atom (command : Command) : Atom :=
  .expression [.symbol "HOL:Step", command.key, command.request]

def commandsAtom (commands : List Command) : Atom :=
  Premises.keys (commands.map Command.atom)

def environment (source : Atom) (commands : List Command) : Subst :=
  [("commands", commandsAtom commands), ("state", source)]

def stepEnvironment (source : Atom) (command : Command) : Subst :=
  ProofEvents.environment source command.key command.request

/-- The endpoints are complete source states, not bare theorem supports. -/
inductive Trace (state : State) : Atom → List Command → Atom → Prop
  | nil (source : Atom) : Trace state source [] source
  | cons {before middle after : Atom} {command : Command} {rest : List Command}
      (event : PureReturns program (stepEnvironment before command) state
        (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"])
        state (.expression [.symbol "Some", middle]))
      (tail : Trace state middle rest after) : Trace state before (command :: rest) after

theorem Trace.append {state : State} {before middle after : Atom} {first second : List Command}
    (left : Trace state before first middle) (right : Trace state middle second after) :
    Trace state before (first ++ second) after := by
  induction left with
  | nil => exact right
  | cons event _ ih => exact .cons event (ih right)

/-- A pause retains the exact intermediate source state, including the
cache and receipts. Endpoints determine where the suffix may resume. -/
theorem Trace.split {state : State} {before after : Atom} {first second : List Command}
    (trace : Trace state before (first ++ second) after) :
    ∃ middle : Atom, Trace state before first middle ∧ Trace state middle second after := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil _, trace⟩
  | cons command commands ih =>
      cases trace with
      | cons event tail =>
          obtain ⟨middle, firstPath, secondPath⟩ := ih tail
          exact ⟨middle, .cons event firstPath, secondPath⟩

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.filter (fun row => row.head == "hol-light:run-from"))[0]'(by decide)

private def consBody : Atom :=
  .expression [.symbol "case",
    .expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"],
    .expression [
      .expression [.expression [.symbol "Some", .var "next"],
        .expression [.symbol "hol-light:run-from", .var "next", .var "rest"]],
      .expression [.var "refused", .symbol "None"]]]

private def cases : SpaceSemantics.Cases :=
  [(.symbol "HOL:Nil", .expression [.symbol "Some", .var "state"]),
    (.expression [.symbol "HOL:Cons", .expression [.symbol "HOL:Step", .var "key", .var "request"],
      .var "rest"], consBody),
    (.var "malformed", .symbol "None")]

private theorem shape : equation.body = .expression [.symbol "case", .var "commands",
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide

private theorem clause (source : Atom) (commands : List Command) :
    clauses program "hol-light:run-from" [source, commandsAtom commands] =
      [.evaluate (environment source commands) equation.body] := by
  rw [clauses_use_only_the_named_equations]
  have unique : program.equations.filter (fun row => row.head == "hol-light:run-from") = [equation] := rfl
  rw [unique]
  have formals : equation.arguments = [.var "state", .var "commands"] := by decide
  simp [formals, environment, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup]

private theorem step_capture_stage (bindings : Subst) (state : State) (fuel : Nat) :
    run program (fuel + 14)
      {state, control := .evaluate bindings
        (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"])} =
      run program fuel
        { state := state,
          control := .sequence (clauses program "hol-light:step"
            [applySubst bindings (.var "state"), applySubst bindings (.var "key"),
              applySubst bindings (.var "request")]) [],
          frames := [.sequence [] [], .sequence [] [], .sequence [] []]} := by
  have dispatched : program.equations.any (fun row => row.head == "hol-light:step") = true := by decide
  have raw0 : argumentIsRaw program "hol-light:step" 0 = false := by decide
  have raw1 : argumentIsRaw program "hol-light:step" 1 = false := by decide
  have raw2 : argumentIsRaw program "hol-light:step" 2 = false := by decide
  have ordinary : ioHead "hol-light:step" = false := by decide
  have authored : StdLib.known "hol-light:step" = false := by decide
  have saturated : 3 ∈ arities program "hol-light:step" := by decide
  simp [run, step, dispatched, raw0, raw1, raw2, ordinary, authored, -application,
    application_saturated (values := [applySubst bindings (.var "state"),
      applySubst bindings (.var "key"), applySubst bindings (.var "request")]) saturated]

private theorem step_capture_returns (first second : Subst) (state : State) (answer : Atom)
    (same : [applySubst first (.var "state"), applySubst first (.var "key"),
        applySubst first (.var "request")] =
      [applySubst second (.var "state"), applySubst second (.var "key"),
        applySubst second (.var "request")])
    (returned : PureReturns program first state
      (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"]) state answer) :
    PureReturns program second state
      (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"]) state answer := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program first state state _ _ returned
  have enough := completed_run_more_fuel program fuel 14 _ state [answer] [] [] completed
  have joined : run program (fuel + 14)
      {state, control := .evaluate first
        (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"])} =
      run program (fuel + 14)
      {state, control := .evaluate second
        (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"])} := by
    rw [step_capture_stage, step_capture_stage, same]
  rw [joined] at enough
  exact completed_run_has_path program (fuel + 14) _ state [answer] [] [] enough

/-- Replay exactly the retained command sequence through the actual source
loop. No command is replaced by an assumed logical macro step. -/
theorem authored_run_from {state : State} {before after : Atom} {commands : List Command}
    (trace : Trace state before commands after) (bindings : Subst) (stateName commandsName : String)
    (stateCaptured : applySubst bindings (.var stateName) = before)
    (commandsCaptured : applySubst bindings (.var commandsName) = commandsAtom commands) :
    PureReturns program bindings state
      (.expression [.symbol "hol-light:run-from", .var stateName, .var commandsName]) state
      (.expression [.symbol "Some", after]) := by
  induction trace generalizing bindings stateName commandsName with
  | nil source =>
      apply authored_variable_call_returns program bindings (environment source []) state state
        "hol-light:run-from" [stateName, commandsName] equation.body _
        (by decide) (by decide) (by decide) _ _ (by decide)
      · simpa only [List.map_cons, List.map_nil, stateCaptured, commandsCaptured] using clause source []
      · rw [shape]
        apply case_returns program (environment source []) (environment source []) state state state
          (.var "commands") (.symbol "HOL:Nil") (.expression [.symbol "Some", .var "state"])
          _ _ cases (read_cases_encoded cases)
        · exact variable_returns program _ state "commands"
        · simp [cases, environment, commandsAtom, Premises.keys, SpaceSemantics.selectCase,
            SpaceSemantics.matchValue, matchAtom]
        · simpa [environment, applySubst, Subst.lookup] using
            unary_constructor_returns program (environment source []) state "Some" "state" (by decide) (by decide)
  | @cons before middle after command rest event tail ih =>
      let bound : Subst := [("rest", commandsAtom rest), ("request", command.request),
        ("key", command.key)] ++ environment before (command :: rest)
      let nextBound : Subst := ("next", middle) :: bound
      apply authored_variable_call_returns program bindings (environment before (command :: rest)) state state
        "hol-light:run-from" [stateName, commandsName] equation.body _
        (by decide) (by decide) (by decide) _ _ (by decide)
      · simpa only [List.map_cons, List.map_nil, stateCaptured, commandsCaptured] using clause before (command :: rest)
      · rw [shape]
        apply case_returns program (environment before (command :: rest)) bound state state state
          (.var "commands") (commandsAtom (command :: rest)) consBody _ _ cases
          (read_cases_encoded cases)
        · exact variable_returns program _ state "commands"
        · simp [cases, bound, environment, commandsAtom, Command.atom, Premises.keys,
            SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
            matchAtom, Subst.lookup]
        · apply case_returns program bound nextBound state state state
            (.expression [.symbol "hol-light:step", .var "state", .var "key", .var "request"])
            (.expression [.symbol "Some", middle])
            (.expression [.symbol "hol-light:run-from", .var "next", .var "rest"]) _ _
            [(.expression [.symbol "Some", .var "next"],
              .expression [.symbol "hol-light:run-from", .var "next", .var "rest"]),
              (.var "refused", .symbol "None")]
            (by decide)
          · exact step_capture_returns (stepEnvironment before command) bound state _
              (by simp [bound, stepEnvironment, ProofEvents.environment, environment, applySubst, Subst.lookup]) event
          · simp [nextBound, bound, environment, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
              SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]
          · exact ih nextBound "next" "rest" rfl rfl

/-- Uninterrupted replay and replay in two chunks return the same endpoint.
This law concerns complete proof-event boundaries, not answer-stream pauses. -/
theorem authored_run_from_split {state : State} {before after : Atom} {first second : List Command}
    (trace : Trace state before (first ++ second) after) :
    ∃ middle : Atom,
      PureReturns program (environment before (first ++ second)) state
        (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"]) state
        (.expression [.symbol "Some", after]) ∧
      PureReturns program (environment before first) state
        (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"]) state
        (.expression [.symbol "Some", middle]) ∧
      PureReturns program (environment middle second) state
        (.expression [.symbol "hol-light:run-from", .var "state", .var "commands"]) state
        (.expression [.symbol "Some", after]) := by
  obtain ⟨middle, firstPath, secondPath⟩ := trace.split
  exact ⟨middle, authored_run_from trace _ "state" "commands" rfl rfl,
    authored_run_from firstPath _ "state" "commands" rfl rfl,
    authored_run_from secondPath _ "state" "commands" rfl rfl⟩

end Mettapedia.Languages.HOLLight.MeTTa.SourceReplay
