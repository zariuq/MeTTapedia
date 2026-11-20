import Mettapedia.Languages.MeTTa.PeTTa.LambdaStagingDepth
import Mettapedia.Languages.MeTTa.PeTTa.ScopedSource

/-!
Run the independently authored operand fixture through the shared source
reader, lambda preparation and existing evaluator. No alternate evaluator or
fixture-specific parsing rules are introduced here. The fixture has no private
clauses; general preparation of dynamically changing programs is separate.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa

def source : String := include_str "constructor-operands.metta"

def main : IO Unit := do
  let program ← match SpaceSemantics.readProgram source with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let queries ← program.initializers.mapM fun expression => do
    let result := LambdaStaging.stage program ∅ {} expression
    unless result.table.code.isEmpty do
      throw (IO.userError "operand fixture unexpectedly contains private clauses")
    pure result.expression
  let initial : Unifying.Configuration :=
    {state := Effects.loaded program,control := .returned []}
  let results := ScopedSource.requests program 1000 initial queries
  unless results.length = queries.length do
    throw (IO.userError "operand fixture stopped before its last request")
  for result in results do
    match result with
    | .complete _ answers _ output =>
        unless output.isEmpty do throw (IO.userError "unexpected printed effects")
        IO.println (String.intercalate " " (answers.map Atom.toString))
    | .exhausted _ => throw (IO.userError "operand fixture exhausted its allowance")
    | .fault reason _ => throw (IO.userError (reprStr reason))
