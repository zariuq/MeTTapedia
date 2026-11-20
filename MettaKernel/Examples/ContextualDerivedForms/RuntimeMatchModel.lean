import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaRuntimeMatchControls

/-! Executable consumer of the written/runtime match distinction. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaRuntimeMatchControls

def describe (label : String) (result : Unifying.Outcome) : IO Unit := do
  match Unifying.shown result with
  | .printed output answers =>
      IO.println s!"{label}: output={reprStr (output.map Atom.toString)} answers={reprStr (answers.map Atom.toString)}"
  | .fault reason => throw (IO.userError s!"{label}: {reprStr reason}")
  | .other => throw (IO.userError s!"{label}: unfinished source computation")

def main : IO Unit := do
  describe "escaping" (Unifying.run registry 100 (ScopedSource.enter 0 [] state escaping))
  describe "held" (Unifying.run registry 100 (ScopedSource.enter 0 [] state held))
  describe "open-row" (Unifying.run registry 100 (ScopedSource.enter 0 [] state openRow))
  describe "written" (Unifying.run registry 100 (ScopedSource.enter 0 [] state
    (call "match" [.symbol "&self",call "row" [.symbol "a"],call "println!" [.grounded (.int 9)]])))
