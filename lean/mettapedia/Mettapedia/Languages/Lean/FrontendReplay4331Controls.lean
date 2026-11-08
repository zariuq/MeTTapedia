import Mettapedia.Languages.Lean.FrontendReplay4331

/-!
Live qualification of replayed imports and syntax-changing commands. These
are host integration tests, separate from the portable scope theorems.
-/

namespace Mettapedia.Languages.Lean.FrontendReplay4331.Controls

open _root_.Lean _root_.Lean.Elab

def fixture : System.FilePath := "Mettapedia/Languages/Lean/FrontendScopeFixture.lean"

def droppedEventRefused (context : Parser.InputContext) (initial : Frontend.State)
    (trace : Trace) (opening : String) : IO Unit := do
  let some index := trace.records.findIdx? (fun record => record.source.startsWith opening)
    | throw (IO.userError ("missing control command: " ++ opening))
  let changed := (trace.records.toList.eraseIdx index).toArray
  let refused ← try
    let _ ← (replayCommands changed { inputCtx := context }).run initial
    pure false
  catch error =>
    unless error.toString.contains "grammar state diverged before byte" do throw error
    pure true
  unless refused do throw (IO.userError ("dropped grammar event was accepted: " ++ opening))

#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let input ← IO.FS.readFile fixture
  IO.println "Scope replay control: capture"
  let trace ← capture input `Mettapedia.Languages.Lean.FrontendScopeFixture
  let (context, _, initial) ← initialState input `Mettapedia.Languages.Lean.FrontendScopeFixture
  IO.println "Scope replay control: positive replay"
  let (rows, _) ← (replayCommands trace.records { inputCtx := context }).run initial
  unless rows.size == 25 do
    throw (IO.userError s!"scope fixture command count changed: {rows.size}")
  IO.println "Scope replay control: dropped local notation"
  droppedEventRefused context initial trace "local notation"
  IO.println "Scope replay control: dropped scoped activation"
  droppedEventRefused context initial trace "open scoped"
  IO.println "Scope replay agrees; dropping local notation or scoped activation is refused"

end Mettapedia.Languages.Lean.FrontendReplay4331.Controls
