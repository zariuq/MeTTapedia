import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagingControls
import Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth

/-! Execute the total lambda-preparation interface and its source consumer. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStagingControls

def prepared (expression : Atom) : LambdaStaging.Result := LambdaStaging.stage registry ∅ {} expression

def execute (expression : Atom) : Unifying.Outcome :=
  let result := prepared expression
  Unifying.run registry 100 (ScopedSource.enter 0 result.table.code Effects.empty result.expression)

def report (label : String) (expression : Atom) : IO Unit := do
  match execute expression with
  | .complete _ answers _ output =>
      unless output.isEmpty do throw (IO.userError s!"{label}: unexpected printed effects")
      IO.println s!"{label}: {reprStr (answers.map Atom.toString)}"
  | .exhausted _ => IO.println s!"{label}: suspended"
  | .fault reason _ => throw (IO.userError s!"{label}: {reprStr reason}")

def main : IO Unit := do
  IO.println s!"code: {reprStr ((prepared nested).table.code.map (·.head))}"
  IO.println s!"cursor: {(prepared nested).table.cursor}"
  report "nested" nested
  IO.println s!"quoted-code: {(prepared quoted).table.code.length}"
  report "unselected" unused
  report "held" held
  report "frozen-future-head" futureHead
  report "future-arguments" futureArguments
