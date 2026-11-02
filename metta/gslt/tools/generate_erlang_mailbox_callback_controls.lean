import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxExecution
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxValueAdmission

/-! Callback component controls with source-model waiting worlds. Pending
accounts are opaque carriers; no kernel execution or scheduler is simulated
by this generator. Quoted inputs are bound once before raw argument passing. -/

set_option maxRecDepth 32768

open Mettapedia.Languages.Erlang
open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorMailboxExecution
open ErlangActorWorldWire

namespace ErlangMailboxCallbackControls

def data (source : Value) : Term := InferenceCettaWire.encodePattern (ErlangCompilation.value source)
def box (source : Mailbox Value) : Term := InferenceCettaWire.encodePattern (ErlangMailbox.mailbox ErlangCompilation.value source)
def machine (raw : Bool) (source : MachineState) : Term :=
  if raw then .application "+" [.natural 1, .natural 2]
  else .application "StoredMachine" [.string (reprStr source)]

def payload : Value := .closure 1 (.recursive 17 1) [.literal (.atom "λ🙂"), .pid 9]
def history : Term := record (.symbol "earlier-first") (record (.symbol "earlier-second") (.symbol "LNil"))
def account : Term := .application "MailboxAccount" [.symbol "completed", .natural 3, .natural 2]
def continuation : Term := .application "ContinuationData" [.application "+" [.natural 5, .natural 6]]

structure Control where
  label : String
  identity : Nat
  action : Term
  box : Term
  machine : Term
  continuation : Term
  result : Term
  system : Term
  expected : Term
  wrong : Term

def pending (label : String) (identity : Nat) (action : Term) : Control :=
  let carrier := box ⟨[payload], [.literal (.atom "old")], [payload]⟩
  let localMachine := machine true (.request .waitInfinity [])
  let world : Term := .application "PendingWorld" [history, .application "+" [.natural 7, .natural 8]]
  let result : Term := .application "ErRhoKernelPending" [account]
  ⟨label, identity, action, carrier, localMachine, continuation, result, world,
    .application "ErActorMailboxPending" [.natural identity, action, carrier, localMachine, continuation, result, world], world⟩

def waitingSystem : ActorSystem :=
  ⟨⟨#[.literal (.integer 0)], 0⟩,
    [⟨0, .request .waitInfinity [], ⟨[payload], [], []⟩⟩,
     ⟨1, .request .waitInfinity [], ⟨[.literal (.atom "kept"), payload], [], []⟩⟩,
     ⟨2, .request .waitInfinity [], {}⟩],
    [⟨⟨0, 2⟩, payload⟩, ⟨⟨0, 2⟩, payload⟩], 3⟩

def waiting (label : String) (identity : Nat) (raw : Bool) : Except String Control := do
  let some selected := waitingSystem.processes[identity]? | throw "missing source process"
  let .ok none := waitingSystem.execute? identity | throw "source request did not wait"
  if waitingSystem.blocked then throw "pending network was reported blocked"
  let original := world box (machine raw) data waitingSystem history
  let effect := waitingEffect identity account
  let expected := world box (machine raw) data waitingSystem (record effect history)
  let wrong := world box (machine raw) data waitingSystem (record effect (.symbol "LNil"))
  pure ⟨label, identity, .symbol "ErWait", box selected.mailbox, machine raw selected.machine,
    continuation, .application "ErRhoKernelDone" [boxed "ErWaiting" [box selected.mailbox], account], original, expected, wrong⟩

def malformed (label : String) (action result expected : Term) : Control :=
  let original : Term := .application "OriginalWorld" [history]
  ⟨label, 0, action, box {}, machine true (.request .waitInfinity []), continuation, result,
    original, expected, original⟩

def controls : Except String (List Control) := do
  let first ← waiting "wait-first" 0 false
  let middle ← waiting "wait-middle" 1 false
  let last ← waiting "wait-last" 2 false
  let raw ← waiting "wait-raw-machine" 1 true
  let original : Term := .application "OriginalWorld" [history]
  let bad : Term := .application "UnrecognizedProgress" [account]
  let target : Term := boxed "ErReady" [box {}]
  pure [pending "pending-peek" 0 (.symbol "ErPeek"),
    pending "pending-cursor-peek" 7 (.application "ErCursorPeek" [.string "ErNext", .string "ErAdvanced"]),
    pending "pending-cursor-apply" 1099511627785
      (.application "ErCursorApply" [.string "ErRemove", .string "ErRemoved", .application "EarlierPeekAccount" [account, account]]),
    pending "pending-wait" 3 (.symbol "ErWait"), first, middle, last, raw,
    malformed "refuse-malformed-progress" (.symbol "ErWait") bad
      (.application "ErActorDiagnostic" [.symbol "MailboxProgress", bad, original]),
    malformed "refuse-unknown-action" (.symbol "UnknownMailboxAction") (.application "ErRhoKernelDone" [target, account])
      (.application "ErActorDiagnostic" [.symbol "MailboxAction", .symbol "UnknownMailboxAction", original])]

def render (control : Control) : String :=
  let quoted := fun term => "(quote " ++ Term.render term ++ ")"
  let bindings := [("action", control.action), ("box", control.box), ("machine", control.machine),
    ("continuation", control.continuation), ("result", control.result), ("world", control.system),
    ("expected", control.expected), ("wrong", control.wrong)]
  let bindText := String.intercalate " " (bindings.map fun (name, term) => "($" ++ name ++ " " ++ quoted term ++ ")")
  let tail := " $action $box $machine $continuation $result $world)"
  let key := toString control.identity
  "!(let* (" ++ bindText ++
    " ($actual (gslt:er-actor:mailbox-result " ++ key ++ tail ++ "))" ++
    " (println! (ErActorMailboxControl " ++ reprStr control.label ++
      " (== $actual $expected)" ++
      " (== (gslt:er-actor:mailbox-result (+ " ++ key ++ " 0)" ++ tail ++ " $expected)" ++
      " (if (== $actual $wrong) False True))))\n"

end ErlangMailboxCallbackControls

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  let .ok cases := ErlangMailboxCallbackControls.controls | throw (IO.userError "source-model control preparation failed")
  let output := System.FilePath.mk directory
  if ← output.pathExists then throw (IO.userError "output already exists")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "controls.metta") (String.join (cases.map ErlangMailboxCallbackControls.render))
  IO.FS.writeFile (output / "cases.json") (Lean.Json.mkObj [
    ("labels", Lean.toJson (cases.map (·.label))), ("checksPerCase", Lean.toJson (3 : Nat)),
    ("scope", .str "pending and waiting actor mailbox callbacks, raw fields and malformed replies; whole actor/kernel linkage remains separate")]).pretty
