import Mettapedia.Languages.MeTTa.PeTTa.Streaming
import Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth

/-!
Calibration consumer for the streaming composition of the existing source
phases. The shared reader supplies programs; the existing preparation pass
supplies private clauses and residual queries. Public body translation and
full upstream compiler adequacy remain separate obligations.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa

def fixture (label source : String) : IO Unit := do
  let program ← match SpaceSemantics.readProgram source with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let (table,queries) := program.initializers.foldl (fun (table,queries) expression =>
    let result := LambdaStaging.stage program ∅ table expression
    (result.table,queries ++ [result.expression])) (LambdaLifting.Table.mk [] 0 ∅,[])
  let mut world : Streaming.World := {state := Effects.loaded program,privateCode := table.code}
  for query in queries do
    let registry := LiveEquations.atState program world.state
    match Streaming.run registry 3000 (Streaming.enter world query) with
    | .complete reached =>
        world := reached.world
        unless world.output.isEmpty do throw (IO.userError "unexpected printed effect")
        IO.println s!"{label}: {String.intercalate " " ((Streaming.values reached).map Atom.toString)}"
    | .suspended _ => throw (IO.userError s!"{label}: suspended")
    | .fault reason _ => throw (IO.userError s!"{label}: {reprStr reason}")

def main : IO Unit := do
  fixture "frontier" (include_str "constructor-streaming-frontier.metta")
  fixture "operands" (include_str "constructor-operands.metta")
  fixture "faults" (include_str "constructor-faults.metta")
  fixture "lambda" (include_str "lambda-nested-staging.metta")
  fixture "future" (include_str "lambda-future-arguments.metta")
  fixture "demand" (include_str "streaming-demand.metta")
