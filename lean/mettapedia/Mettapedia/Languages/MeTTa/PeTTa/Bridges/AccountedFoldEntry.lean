import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PagedFoldSourceBoundary
import Mettapedia.Languages.MeTTa.PeTTa.PagedFoldLedger

/-!
# Operand source debits joined to retained callback execution

Each operand is executed once by the existing retained evaluator slice. The
receipt contains its actual source-step debit and the exact completed value,
world and I/O boundary. Callback admission happens only after those operands
settle. Refusal keeps the captured operands and their paid debit; it cannot
reconstruct an unpaid pre-operand invocation.

The source-evaluator ledger and fold-host administration remain separate.
Preparation/recognition work and native physical costs are not counted as
source steps by this profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval FoldSourceBoundary

structure Captured (request : Request) where
  values : FoldSourceBoundary.Captured request.program request.caller request.code request.before
  listDebit : Nat
  initialDebit : Nat
  listExact : EvaluatorAccounting.slice request.program listDebit
    {state := request.before, control := .evaluate request.caller request.code.items} =
      (finished values.middle [.expression values.items] [] [], listDebit)
  initialExact : EvaluatorAccounting.slice request.program initialDebit
    {state := values.middle, control := .evaluate request.caller request.code.initial} =
      (finished values.after [values.initial] [] [], initialDebit)

def Captured.paid {request : Request} (captured : Captured request) : Nat := captured.listDebit + captured.initialDebit

structure Settled (program : SpaceSemantics.Program) (entrance : Configuration) where
  endpoint : Configuration
  debit : Nat
  exact : EvaluatorAccounting.slice program debit entrance = (endpoint, debit)

def settle (program : SpaceSemantics.Program) (budget : Nat) (entrance : Configuration) : Settled program entrance :=
  let page := EvaluatorAccounting.slice program budget entrance
  ⟨page.1, page.2, Mettapedia.Machines.MachineCore.runSlice_replay_used (EvaluatorAccounting.core program) budget entrance⟩

theorem Settled.completed {program : SpaceSemantics.Program} {entrance : Configuration}
    (settled : Settled program entrance) (world : Effects.State) (answers : List Atom)
    (completed : EvaluatorAccounting.observe program settled.endpoint = .complete world answers [] []) :
    (theory program).MultiStep entrance (finished world answers [] []) := by
  have endpoint := (EvaluatorAccounting.observe_complete_iff program settled.endpoint world answers [] []).mp completed
  have reached := EvaluatorAccounting.finite_source_path program settled.debit entrance
  rw [settled.exact, endpoint] at reached
  exact reached

theorem Settled.completed_exact {program : SpaceSemantics.Program} {entrance : Configuration}
    (settled : Settled program entrance) (world : Effects.State) (answers : List Atom)
    (completed : EvaluatorAccounting.observe program settled.endpoint = .complete world answers [] []) :
    EvaluatorAccounting.slice program settled.debit entrance = (finished world answers [] [], settled.debit) := by
  rw [settled.exact, (EvaluatorAccounting.observe_complete_iff program settled.endpoint world answers [] []).mp completed]

inductive Preparation (request : Request)
  | reference
  | handoff (saved : Handoff) (paid : Nat)
  | ready (captured : Captured request)

def prepare (listFuel initialFuel : Nat) (request : Request) : Preparation request :=
  if scopeOK : Scoped request.caller request.code then
    let first := settle request.program listFuel
      {state := request.before, control := .evaluate request.caller request.code.items}
    match listDone : EvaluatorAccounting.observe request.program first.endpoint with
    | .complete middle [.expression items] [] [] =>
        let second := settle request.program initialFuel
          {state := middle, control := .evaluate request.caller request.code.initial}
        match initialDone : EvaluatorAccounting.observe request.program second.endpoint with
        | .complete after [initial] [] [] =>
            .ready ⟨⟨items, initial, middle, after, scopeOK,
              first.completed middle [.expression items] listDone,
              second.completed after [initial] initialDone⟩,
              first.debit, second.debit, first.completed_exact middle [.expression items] listDone,
              second.completed_exact after [initial] initialDone⟩
        | outcome => .handoff (.initialOperand items middle outcome) (first.debit + second.debit)
    | outcome => .handoff (.listOperand outcome) first.debit
  else .reference

structure Running (request : Request) where
  captured : Captured request
  execution : PagedFoldSourceBoundary.Session
  source : execution.request = request
  boundary : execution.captured = source ▸ captured.values

inductive Result (request : Request)
  | reference
  | handoff (saved : Handoff) (paid : Nat)
  | referenceFold (captured : Captured request)
  | running (session : Running request)

def resolve (budget : Nat) (request : Request) (captured : Captured request) : Result request :=
  match FoldCallbackExtraction.prepare budget request.program (request.code.callback request.caller)
      captured.values.items captured.values.initial with
  | none => .referenceFold captured
  | some compiled =>
      let execution : PagedFoldSourceBoundary.Session :=
        ⟨request, captured.values,
          PagedFoldAdmission.begin (PagedFoldSourceBoundary.capturedRequest request captured.values)
            ⟨compiled.result, compiled.returns captured.values.after⟩, rfl⟩
      .running ⟨captured, execution, rfl, rfl⟩

def enter (listFuel initialFuel callbackBudget : Nat) (request : Request) : Result request :=
  match prepare listFuel initialFuel request with
  | .reference => .reference
  | .handoff saved paid => .handoff saved paid
  | .ready captured => resolve callbackBudget request captured

def Running.advance {request : Request} (budget : Nat) (session : Running request) : Running request :=
  ⟨session.captured, (PagedFoldSourceBoundary.advance budget session.execution).1,
    session.source, session.boundary⟩

def Running.sourceDebit {request : Request} (session : Running request) : Nat :=
  session.captured.paid + session.execution.execution.current.sourceDebit

theorem refusal_keeps_paid_operands (budget : Nat) (request : Request) (captured : Captured request)
    (refused : FoldCallbackExtraction.prepare budget request.program (request.code.callback request.caller)
      captured.values.items captured.values.initial = none) :
    resolve budget request captured = .referenceFold captured := by simp [resolve, refused]

theorem completed_source_return {request : Request} (session : Running request)
    (world : Effects.State) (value : Atom)
    (completed : session.execution.execution.current.phase = .done world value) :
    FoldSourceBoundary.Evaluates request.program request.caller request.code request.before world value := by
  have source := (PagedFoldSourceBoundary.completed_source_return session.execution world value completed).2
  simpa only [session.source] using source

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldEntry
