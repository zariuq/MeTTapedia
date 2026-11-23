import Mettapedia.ProbabilityTheory.StochasticInference.BinaryLikelihoodEnvelope
import Lean.Data.Json.FromToJson

/-! # Replay metered binary likelihood paths -/

set_option autoImplicit false

namespace Mettapedia.Examples.PLN.DiagnosticPathReplay

open Lean Mettapedia.ProbabilityTheory.StochasticInference
open BinaryLikelihoodEnvelope

abbrev Ratio := Nat × Nat

structure Reading where
  value : Bool
  links : List (Ratio × Ratio)
  processed : Nat
  deriving FromJson

structure Query where
  prior : Ratio
  reports : List Reading
  deriving FromJson

structure Packet where
  queries : List Query
  budget : Nat
  deriving FromJson

private def probability (raw : Ratio) : Except String UnitProbability := do
  if raw.2 = 0 then throw "Expected a positive denominator"
  let some p := UnitProbability.checked (raw.1 / (raw.2 : ℚ)) | throw "Expected a probability in [0, 1]"
  pure p

private def link (raw : Ratio × Ratio) : Except String Kernel := do
  let no ← probability raw.1
  let yes ← probability raw.2
  pure (fun b => if b then yes else no)

private def indicator (reading state : Bool) : UnitProbability :=
  if reading = state then ⟨1, zero_le_one, le_rfl⟩ else ⟨0, le_rfl, zero_le_one⟩

private def query (input : Query) : Except String (Option (ℚ × ℚ)) := do
  let prior ← probability input.prior
  let paths ← input.reports.mapM fun report => do
    let links ← report.links.mapM link
    if links.length < report.processed then throw "Processed links exceed the path length"
    pure ((⟨indicator report.value, links⟩ : Path), report.processed)
  pure (pathReadout prior paths)

private def evaluate (packet : Packet) : Except String Json := do
  let work := (packet.queries.map (fun item => (item.reports.map Reading.processed).sum)).sum
  if packet.budget < work then throw "The plan exceeds the work budget"
  let answers ← packet.queries.mapM query
  pure (Json.mkObj [("transfers", toJson work),
    ("answers", toJson (answers.map (Option.map (fun (lo, hi) => ((lo.num, lo.den), (hi.num, hi.den))))))])

end Mettapedia.Examples.PLN.DiagnosticPathReplay

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := do
      let json ← Lean.Json.parse line
      let packet ← Lean.fromJson? json
      Mettapedia.Examples.PLN.DiagnosticPathReplay.evaluate packet
    let response := match result with
      | .ok value => value
      | .error message => Lean.Json.mkObj [("error", Lean.toJson message)]
    output.putStrLn response.compress
    output.flush
