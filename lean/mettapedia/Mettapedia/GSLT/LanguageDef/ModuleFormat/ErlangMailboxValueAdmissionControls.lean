import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxValueExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxCursorAgreement

/-! Uniform source-value admission includes non-ASCII atoms, arbitrarily
large word encodings and recursive captures. Negative sort controls keep
constructor spelling, payload typing and operational enabling distinct. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.AdmissionControls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Erlang
open Mettapedia.GSLT.LanguageDef.WellSorted
open ErlangCompilation (value)

def captured : Value := .closure 1 (.recursive 17 2)
  [.literal (.atom "λ🙂"), .pid 18446744073709551619, .literal (.integer (-18446744073709551619))]

def sample : Mailbox Value := ⟨[captured], [], [captured, .literal (.atom "λ🙂") ]⟩

theorem all_six_requests_admitted :
    Model.Sorted (node "ErPeek" [mailbox value sample]) ∧
    Model.Sorted (node "ErNext" [mailbox value sample]) ∧
    Model.Sorted (node "ErRemove" [mailbox value sample]) ∧
    Model.Sorted (node "ErWait" [mailbox value sample]) ∧
    Model.Sorted (node "ErDeliver" [value captured, mailbox value sample]) ∧
    Model.Sorted (node "ErWake" [value captured, mailbox value sample]) :=
  ⟨Admission.peek_sorted _, Admission.next_sorted _, Admission.remove_sorted _, Admission.wait_sorted _,
    Admission.deliver_sorted _ _, Admission.wake_sorted _ _⟩

theorem typed_wake_still_disabled (target : Pattern) :
    ¬ ContextualStep.Step Runner.base language (node "ErWake" [value captured, mailbox value sample]) target := by
  apply nonempty_wake_no_step
  decide +kernel

def malformed : List Pattern := [
  node "ErPeek" [node "ErMailbox" [node "ErZero", node "ErValuesNil", node "ErValuesNil"]],
  node "ErDeliver" [node "ErZero", mailbox value sample],
  node "ErDeliver" [node "ErPid" [.collection .vec [node "R16Nibble16"] none], mailbox value sample],
  node "ErDeliver" [node "ErClosure" [node "ErZero", node "ErLambdaFunction" [ErlangCompilation.code 0],
    node "ErEnvironmentCons" [node "ErZero", node "ErEnvironmentNil"]], mailbox value sample]]

def accepted (pattern : Pattern) : Bool :=
  checkOpenPatternWellSorted Model.environment.language Model.environment.free [] (.base "ErMailboxConfig") pattern

#guard malformed.all (fun pattern => !accepted pattern)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.AdmissionControls
