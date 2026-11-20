import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorControls

/-! Executable consumer of retained decisions and fresh compiler locals. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaConstructorControls

def report (label : String) (outcome : Unifying.Outcome) : IO Unit := do
  match outcome with
  | .complete _ answers _ _ => IO.println s!"{label}: {reprStr (answers.map Atom.toString)}"
  | .exhausted _ => IO.println s!"{label}: suspended"
  | .fault reason _ => throw (IO.userError s!"{label}: {reprStr reason}")

def main : IO Unit := do
  report "retained-data" (execute lateProgram 100 frozenLate)
  report "known-call" (execute lateProgram 100 (call "late" []))
  report "raw-cutoff" (execute emptyProgram 1 (call "late" []))
  report "frozen-cutoff" (execute emptyProgram 1 frozenLate)
  report "empty" (execute emptyProgram 100
    (ConstructorDataHeads.emit emptyProgram (.symbol "empty") []))
  report "input" (Unifying.run emptyProgram 100 inputRequest)
  match Unifying.unifyBinding original (.var "local") (.var "source") with
  | .ok bound =>
      IO.println s!"source-key: {(Unifying.resolve bound (.var "source")).toString}"
      IO.println s!"local-key: {(Unifying.resolve bound (.var "local")).toString}"
      IO.println s!"projection-exact: {decide (Unifying.eraseLocal "local" bound = original)}"
  | _ => throw (IO.userError "fresh local unexpectedly refused")
