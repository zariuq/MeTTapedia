import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopeControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopePreservationControls

/-! Executable consumer of the scoped-import controls. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopeControls

def describe (label : String) (result : Unifying.Outcome) : IO Unit := do
  match Unifying.observed result with
  | .answers answers => IO.println s!"{label}: {reprStr (answers.map Atom.toString)}"
  | .fault reason => throw (IO.userError s!"{label}: {reprStr reason}")
  | .other => throw (IO.userError s!"{label}: unfinished source computation")

def main : IO Unit := do
  describe "parse" (Unifying.run registry 100 (ScopedSource.enter 0 [] Effects.empty parsed))
  describe "rows" (Unifying.run registry 100 (ScopedSource.enter 0 [] rowState enumerated))
  describe "assignment" (Unifying.run registry 150 (ScopedSource.enter 0 [] Effects.empty assigned))
  describe "input" (Unifying.run registry 100
    {ScopedSource.enter 0 [] Effects.empty inputRequest with input := [.var "x#0"]})
  for result in sessionResults do describe "session" result
  describe "reset-counter" (Unifying.run (LiveEquations.atState registry savedCell) 100
    (ScopedSource.enter 0 [] savedCell (call "pick" [.symbol "a"])))
