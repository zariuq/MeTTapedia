import Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.AccountedFoldEntry

/-!
# Paid operand capture for integer-sort specialization

The operand executes once in the actual evaluator. Its completed world and
source-step debit survive integer admission failure. A non-integer operand
continues at the ordinary primitive receiver, not at the original expression.
I/O, faults, multiple answers and pauses retain the exact operand endpoint.
The envelope keeps the original request as runtime data for resumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics

structure Request where
  program : Program
  caller : Subst
  before : Effects.State
  operand : Atom

def Request.start (request : Request) : Configuration :=
  {state := request.before, control := .evaluate request.caller request.operand}

def Request.receiver (request : Request) : Frame :=
  .argument request.caller (.function "msort") [] [] 0

def Request.sourceStart (request : Request) : Configuration :=
  {state := request.before, control := .evaluate request.caller (IntegerSortSource.source request.operand)}

theorem source_enters_operand (request : Request) :
    (theory request.program).MultiStep request.sourceStart (withFrames request.start [request.receiver]) := by
  apply Mettapedia.GSLT.GSLT.MultiStep.step (S := theory request.program)
    (step_transition (show Eval.step request.program request.sourceStart = some
      {state := request.before, control := .arguments request.caller (.function "msort") [request.operand] [] 0}
      from by simp [Eval.step, Request.sourceStart, IntegerSortSource.source, ioHead, StdLib.known]))
  apply Mettapedia.GSLT.GSLT.MultiStep.step (S := theory request.program)
    (step_transition (show Eval.step request.program
      {state := request.before, control := .arguments request.caller (.function "msort") [request.operand] [] 0} =
      some (withFrames request.start [request.receiver]) from by
        simp [Eval.step, Request.start, Request.receiver, withFrames, argumentIsRaw, StdLib.known, StdLib.rawArgument]))
  exact .refl _

structure Captured (request : Request) where
  after : Effects.State
  values : List Int
  operandDebit : Nat
  exact : EvaluatorAccounting.slice request.program operandDebit request.start =
    (finished after [.expression (StdLib.integerAtoms values)] [] [], operandDebit)

theorem Captured.operand_returns {request : Request} (captured : Captured request) :
    PureReturns request.program request.caller request.before request.operand captured.after
      (.expression (StdLib.integerAtoms captured.values)) := by
  have path := EvaluatorAccounting.finite_source_path request.program captured.operandDebit request.start
  rw [captured.exact] at path
  exact path

def Captured.worker {request : Request} (captured : Captured request) :=
  Mettapedia.Algorithms.CountedKeySort.run id captured.values

theorem Captured.source_returns {request : Request} (captured : Captured request) :
    PureReturns request.program request.caller request.before (IntegerSortSource.source request.operand)
      captured.after (.expression (StdLib.integerAtoms captured.worker.rows)) :=
  IntegerSortSource.worker_source_return request.program request.caller request.before captured.after
    request.operand captured.values captured.operand_returns

structure PrimitiveFallback (request : Request) where
  after : Effects.State
  value : Atom
  operandDebit : Nat
  exact : EvaluatorAccounting.slice request.program operandDebit request.start =
    (finished after [value] [] [], operandDebit)

def PrimitiveFallback.receiver {request : Request} (fallback : PrimitiveFallback request) : Configuration :=
  {state := fallback.after,
   control := .arguments request.caller (.function "msort") [] [fallback.value] 1}

inductive Preparation (request : Request)
  | admitted (captured : Captured request)
  | primitive (captured : PrimitiveFallback request)
  | handoff (settled : AccountedFoldEntry.Settled request.program request.start)

def prepare (budget : Nat) (request : Request) : Preparation request :=
  let settled := AccountedFoldEntry.settle request.program budget request.start
  match completed : EvaluatorAccounting.observe request.program settled.endpoint with
  | .complete after [value] [] [] =>
      let fallback : PrimitiveFallback request :=
        ⟨after, value, settled.debit, settled.completed_exact after [value] completed⟩
      match value with
      | .expression items =>
          match decoded : StdLib.integers items with
          | none => .primitive fallback
          | some values =>
              .admitted ⟨after, values, settled.debit, by
                rw [StdLib.integers_exact items values decoded]
                exact settled.completed_exact after [.expression items] completed⟩
      | _ => .primitive fallback
  | _ => .handoff settled

structure Envelope where
  request : Request
  result : Preparation request

def enter (budget : Nat) (request : Request) : Envelope := ⟨request, prepare budget request⟩

theorem handoff_endpoint_is_reached (request : Request)
    (settled : AccountedFoldEntry.Settled request.program request.start) :
    (theory request.program).MultiStep request.start settled.endpoint := by
  have path := EvaluatorAccounting.finite_source_path request.program settled.debit request.start
  rw [settled.exact] at path
  exact path

open private path_trans from Mettapedia.Languages.MeTTa.PeTTa.Eval in
/-- Paused or effectful operands retain the actual enclosing source receiver.
Appending the receiver preserves the operand's own pending frames and I/O. -/
theorem handoff_is_reached_under_source_receiver (request : Request)
    (settled : AccountedFoldEntry.Settled request.program request.start) :
    (theory request.program).MultiStep request.sourceStart
      (withFrames settled.endpoint [request.receiver]) :=
  path_trans (source_enters_operand request)
    (path_with_caller_frames request.program [request.receiver] (handoff_endpoint_is_reached request settled))

theorem fallback_retains_paid_source_result {request : Request} (fallback : PrimitiveFallback request) :
    PureReturns request.program request.caller request.before request.operand fallback.after fallback.value := by
  have path := EvaluatorAccounting.finite_source_path request.program fallback.operandDebit request.start
  rw [fallback.exact] at path
  exact path

/-- The next ordinary primitive step uses the captured value and world. -/
theorem fallback_step {request : Request} (fallback : PrimitiveFallback request)
    (world : Effects.State) (answers : List Atom)
    (computed : StdLib.apply fallback.after "msort" [fallback.value] = .ok (world, answers)) :
    Eval.step request.program fallback.receiver =
      some {fallback.receiver with state := world, control := .returned answers} := by
  simp [Eval.step, PrimitiveFallback.receiver, ioHead, StdLib.known, computed]

namespace Controls

open MeTTaIL.WireKit

def request : Request :=
  ⟨{equations := [], declarations := []}, [], {core := []},
    apply "let" [.var "ignored", apply "add-atom" [.symbol "&self", number 9],
      apply "quote" [.expression [number 3, number 1, number 3]]]⟩

inductive View
  | admitted (core : List Atom) (values : List Int) (paid : Nat)
  | primitive (core : List Atom) (value : Atom) (paid : Nat)
  | handoff (core output : List Atom) (paid : Nat)
  deriving DecidableEq

def view {request : Request} : Preparation request → View
  | .admitted captured => .admitted captured.after.core captured.values captured.operandDebit
  | .primitive captured => .primitive captured.after.core captured.value captured.operandDebit
  | .handoff settled => .handoff settled.endpoint.state.core settled.endpoint.output settled.debit

def valuesOnly : View → Option (List Atom × List Int)
  | .admitted core values _ => some (core, values)
  | _ => none

theorem operand_effect_is_kept_once : valuesOnly (view (prepare 100 request)) =
    some ([number 9], [3, 1, 3]) := by decide +kernel

def unsupported : Request :=
  {request with operand := apply "let" [.var "ignored", apply "add-atom" [.symbol "&self", number 9],
    apply "quote" [.expression [Effects.boolean true]]]}

def primitiveOnly : View → Option (List Atom × Atom)
  | .primitive core value _ => some (core, value)
  | _ => none

theorem unsupported_type_keeps_operand_effect : primitiveOnly (view (prepare 100 unsupported)) =
    some ([number 9], .expression [Effects.boolean true]) := by decide +kernel

theorem zero_budget_retains_original_world : view (prepare 0 request) = .handoff [] [] 0 := by decide +kernel

def printed : Request := {request with operand := apply "println!" [number 7]}

def outputOnly : View → List Atom
  | .handoff _ output _ => output
  | _ => []

theorem printed_output_is_not_replayed_as_untouched_input : outputOnly (view (prepare 100 printed)) = [number 7] := by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.IntegerSortEntry
