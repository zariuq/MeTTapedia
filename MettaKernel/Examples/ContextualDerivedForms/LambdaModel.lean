import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLambdaControls

/-! Executable consumer of private-clause formation and actual source firing.
Recursive lambda translation and the general scope/readout invariant remain
explicit obligations in the coverage ledger. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.ContextualTransform
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLambdaControls

def describe (label : String) (result : Unifying.Outcome) : IO Unit := do
  match Unifying.shown result with
  | .printed output answers =>
      IO.println s!"{label}: output={reprStr (output.map Atom.toString)} answers={reprStr (answers.map Atom.toString)}"
  | .fault reason => throw (IO.userError s!"{label}: {reprStr reason}")
  | .other => throw (IO.userError s!"{label}: unfinished source computation")

def main : IO Unit := do
  IO.println s!"formation: name={lifted.installed.head} captures={reprStr lifted.captured}"
  describe "capture" (runLifted request)
  describe "held" (runLifted heldRequest)
  describe "late" (runLifted lateCaptureRequest)
  describe "public-space" (runLifted (call "collapse" [call "get-atoms" [.symbol "&self"]]))
  describe "public-remove" (runLifted removeThenCall)
  describe "closed" (Unifying.run registry 100
    (LambdaLifting.enter closed Effects.empty (.expression [closed.closure,.symbol "a"])))
  IO.println s!"capture-order: {reprStr (LambdaLifting.captures [.var "x"] (call "row" [.var "b",.var "a",.var "b",.var "x",.var "a"]))}"
  IO.println s!"stale-private-cache: {PeTTaActivation.callable (Unifying.codeRegistry registry [installed]) "lambda_1"}/{PeTTaCallCache.lookup (Unifying.codeRegistry registry [installed]) oldNegativeCache "lambda_1"}"
  describe "raw-collision" (Unifying.run registry 100
    (Unifying.startWithCode closed.table.code Effects.empty suffixCollision))
  describe "scoped-collision" (Unifying.run registry 100
    (LambdaLifting.enter closed Effects.empty suffixCollision))
