import Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth
import Mettapedia.Languages.MeTTa.PeTTa.ScopedSource

/-!
Calibrate private lambda bodies containing constructor errors and answerless
operands. The shared reader and preparation pass supply a single retained
private-code inventory; the existing evaluator executes successive requests.
The fixture contains no public equations requiring a separate body translator.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa

def source : String := include_str "constructor-faults.metta"

def main : IO Unit := do
  let program ← match SpaceSemantics.readProgram source with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  unless program.equations.isEmpty do
    throw (IO.userError "fault fixture unexpectedly contains public equations")
  let (table,queries) := program.initializers.foldl (fun (table,queries) expression =>
    let result := LambdaStaging.stage program ∅ table expression
    (result.table,queries ++ [result.expression])) (LambdaLifting.Table.mk [] 0 ∅,[])
  let initial : Unifying.Configuration :=
    {state := Effects.loaded program,control := .returned [],privateCode := table.code}
  let results := ScopedSource.requests program 1000 initial queries
  unless results.length = queries.length do
    throw (IO.userError "fault fixture stopped before its last request")
  for result in results do
    match result with
    | .complete _ answers _ output =>
        unless output.isEmpty do throw (IO.userError "unexpected printed effects")
        IO.println (String.intercalate " " (answers.map Atom.toString))
    | .exhausted _ => throw (IO.userError "fault fixture exhausted its allowance")
    | .fault reason _ => throw (IO.userError (reprStr reason))
