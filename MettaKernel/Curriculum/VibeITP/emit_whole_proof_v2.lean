import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofControls
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
import Lean.Data.Json.Printer

/-! Untrusted export of the whole supplied-witness guest and its reference
requests. Finite runtime comparisons do not establish implementation refinement.
The scalar/list data library is an explicit input. -/

open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2
open Lean (toJson)

deriving instance DecidableEq for Outcome

private def outcome : Outcome → String
  | .value term => "(nik:Value " ++ MeTTaEmit.data term ++ ")"
  | .failure => "nik:Failure"
  | .exhausted => "nik:Exhausted"

def main (arguments : List String) : IO UInt32 := do
  let [library, output] := arguments |
    throw (IO.userError "expected shared-data-library and output-directory")
  let shared ← IO.FS.readFile library
  let directory : System.FilePath := output
  IO.FS.createDirAll directory
  let program := wholeProgram
  let requests := Controls.requests
  for query in requests do
    let actual := apply program productDivisionHost query.fuel query.head query.arguments
    unless actual = query.expected do
      throw (IO.userError s!"authored/reference disagreement in {query.name}: {outcome actual}")
  let code := MeTTaEmit.program program
  let calls := requests.map fun query =>
    "!(collapse " ++ MeTTaEmit.request program query.fuel query.head query.arguments ++ ")"
  IO.FS.writeFile (directory / "vibe-proof-v2.generated.metta") (shared ++ "\n" ++ code)
  IO.FS.writeFile (directory / "vibe-proof-v2.probe.metta")
    (shared ++ "\n" ++ code ++ String.intercalate "\n" calls ++ "\n")
  IO.FS.writeFile (directory / "vibe-proof-v2.expected")
    (String.intercalate "\n" (requests.map fun query => "[(" ++ outcome query.expected ++ ")]") ++ "\n")
  let records := requests.map fun query => Lean.Json.mkObj [
    ("name", .str query.name), ("head", .str query.head), ("fuel", toJson query.fuel),
    ("request", .str (MeTTaEmit.request program query.fuel query.head query.arguments)),
    ("expected", .str (outcome query.expected))]
  IO.FS.writeFile (directory / "vibe-proof-v2.json") (Lean.Json.pretty (Lean.Json.mkObj [
    ("equations", toJson program.length), ("heads", toJson (program.map Equation.head).eraseDups.length),
    ("probes", .arr records.toArray)]) ++ "\n")
  return 0
