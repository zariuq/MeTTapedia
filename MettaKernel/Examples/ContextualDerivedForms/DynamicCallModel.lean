import Mettapedia.Languages.MeTTa.PeTTa.DynamicCallControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaDynamicContexts

/-! Executable consumer of the runtime-call source controls and context laws.
The file fixtures supply separate reference/native calibration; no source
reader or C implementation correspondence is asserted by this consumer. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying DynamicCallControls

def describe (label : String) (result : Except String (List Shown)) : IO Unit := do
  let .ok outcomes := result | throw (IO.userError "source forms failed to load")
  for outcome in outcomes do
    match outcome with
    | .printed output answers =>
        IO.println s!"{label}: output={reprStr (output.map Atom.toString)} answers={reprStr (answers.map Atom.toString)}"
    | .fault reason => IO.println s!"{label}: fault={reprStr reason}"
    | .other => throw (IO.userError "source did not complete; not an empty answer")

def main : IO Unit := do
  describe "basic" (execute [pair] basicRequests)
  describe "demand" (execute [holdType, holdForm]
    [call "hold" [call "println!" [num 9]],
     bind (var "f") (held (sym "hold")) (invoke (var "f") [call "println!" [num 9]])])
  describe "recovery" (execute alternatives
    [bind (var "f") (held (sym "alternatives")) (call "collapse" [invoke (var "f") []]),
     call "collapse" [call "match" [sym "&self", call "mark" [], sym "present"]]])
  IO.println s!"pause marks={recoverySaved.state.core.count (call "mark" [])}"
  let some (earned, _) := recoverDynamic [] recoverySaved.frames
    | throw (IO.userError "saved call has no recoverable boundary")
  IO.println s!"retained answers={reprStr ((earned.map Unifying.Answer.value).map Atom.toString)}"
  IO.println s!"resumed marks={reprStr (completedMarks (Unifying.run recoveryProgram 100 recoverySaved))}"
  IO.println s!"restarted marks={reprStr (completedMarks (Unifying.run recoveryProgram 100
    (Unifying.start recoverySaved.state recoveryRequest)))}"
