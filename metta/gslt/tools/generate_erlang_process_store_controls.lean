import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorWorldWire

/-! Process-store controls generated from the independent source operations.
Mailbox and machine fields are opaque carriers here. This does not execute
the sequential controller, mailbox kernel or an actor scheduling policy. -/

set_option maxRecDepth 32768

open Mettapedia.Languages.Erlang
open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorProcessWire ModuleFormat.ErlangActorWorldWire

namespace ErlangProcessStoreControls

def datum (value : Value) : Term := .application "StoredValue" [.string (reprStr value)]

def box (mailbox : Mailbox Value) : Term := .application "StoredMailbox"
  [encodeList datum mailbox.savedRev, encodeList datum mailbox.front, encodeList datum mailbox.rearRev]

def machine (raw : Bool) (state : MachineState) : Term :=
  if raw then .application "+" [.natural 1, .natural 2]
  else .application "StoredMachine" [.string (reprStr state)]

def entry (identity value : Nat) : LocalProcess :=
  ⟨identity, .halted (.ok [.literal (.integer value)]),
    ⟨[.literal (.integer (Int.negSucc value))], [.literal (.integer value)], [.pid identity]⟩⟩

structure Control where
  label : String
  identity : Nat
  processes : List LocalProcess
  replacement : LocalProcess
  raw : Bool := false

def controls : List Control := [
  ⟨"empty", 0, [], entry 0 9, false⟩,
  ⟨"single-present", 0, [entry 0 1], entry 0 9, false⟩,
  ⟨"single-absent", 1, [entry 0 1], entry 1 9, false⟩,
  ⟨"first", 0, [entry 0 1, entry 1 2, entry 2 3], entry 0 9, false⟩,
  ⟨"middle", 1, [entry 0 1, entry 1 2, entry 2 3], entry 1 9, false⟩,
  ⟨"last", 2, [entry 0 1, entry 1 2, entry 2 3], entry 2 9, false⟩,
  ⟨"absent", 10, [entry 0 1, entry 1 2, entry 2 3], entry 10 9, false⟩,
  ⟨"duplicate-key-first", 7, [entry 7 1, entry 7 2, entry 8 3], entry 7 9, false⟩,
  ⟨"duplicate-key-after-prefix", 7, [entry 3 0, entry 7 1, entry 7 2], entry 7 9, false⟩,
  ⟨"large-key", 18446744073709551619, [entry 0 1, entry 18446744073709551619 2], entry 18446744073709551619 9, false⟩,
  ⟨"raw-field-present", 1, [entry 0 1, entry 1 2], entry 1 9, true⟩,
  ⟨"raw-field-absent", 3, [entry 0 1, entry 1 2], entry 3 9, true⟩,
  ⟨"raw-field-prefix", 2, [entry 0 1, entry 1 2, entry 2 3], entry 2 9, true⟩,
  ⟨"replacement-carrier", 1, [entry 0 1, entry 1 2], entry 17 9, false⟩]

def render (control : Control) : String :=
  let encode := process box (machine control.raw)
  let stored := encodeList encode control.processes
  let selected := encodeOption encode (ActorProcessStore.get control.identity control.processes)
  let replaced := encodeList encode (ActorProcessStore.put control.identity control.replacement control.processes)
  let system : ActorSystem := ⟨⟨#[.literal (.integer 0)], 0⟩, control.processes,
    [⟨⟨9, 10⟩, .literal (.atom "first")⟩, ⟨⟨9, 10⟩, .literal (.atom "second")⟩], 20⟩
  let history : Term := record (.symbol "earlier-effect") (.symbol "LNil")
  let effect : Term := .application "StoreEffect" [.natural control.identity]
  let committed := {control.replacement with identity := control.identity}
  let replacementWorld := {system with processes := ActorProcessStore.put control.identity committed system.processes}
  let expectedWorld := world box (machine control.raw) datum replacementWorld (record effect history)
  let quote := fun term => "(quote " ++ Term.render term ++ ")"
  let bindings := [("stored", stored), ("replacement", encode control.replacement),
    ("selected", selected), ("replaced", replaced), ("box", box control.replacement.mailbox),
    ("machine", machine control.raw control.replacement.machine), ("effect", effect),
    ("world", world box (machine control.raw) datum system history), ("expectedWorld", expectedWorld)]
  let bindingsText := String.intercalate " " (bindings.map fun (name, value) => "($" ++ name ++ " " ++ quote value ++ ")")
  let key := toString control.identity
  "!(let* (" ++ bindingsText ++ ") (println! (ErActorStoreControl " ++ reprStr control.label ++
    " (== (gslt:er-actor:get " ++ key ++ " $stored) $selected)" ++
    " (== (gslt:er-actor:put " ++ key ++ " $replacement $stored) $replaced)" ++
    " (== (gslt:er-actor:get (+ " ++ key ++ " 0) $stored) $selected)" ++
    " (== (gslt:er-actor:store " ++ key ++ " $box $machine $effect $world) $expectedWorld))))\n"

end ErlangProcessStoreControls

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected an output directory")
  let output := System.FilePath.mk directory
  if ← output.pathExists then throw (IO.userError "output already exists")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "controls.metta")
    (String.join (ErlangProcessStoreControls.controls.map ErlangProcessStoreControls.render))
  IO.FS.writeFile (output / "cases.json") (Lean.Json.mkObj [
    ("labels", Lean.toJson (ErlangProcessStoreControls.controls.map (·.label))),
    ("checksPerCase", Lean.toJson (4 : Nat)),
    ("scope", .str "loaded pid-keyed process-store operations with opaque record carriers; no actor-controller or complete E0 claim")]).pretty
