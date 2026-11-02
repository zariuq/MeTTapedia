import Mettapedia.Languages.VibeITP.Spec.ProtocolV2Controls
import Mettapedia.Languages.VibeITP.Native.ProtocolV2LogicalControls
import Lean.Data.Json

/-! Export the reference protocol's unchanged test bytes for an external oracle.
This producer does not certify the native executable or its process protocol. -/

open Lean
open Mettapedia.Languages.VibeITP.Spec
open ProtocolV2.Controls

private def resultClass : Verdict → String
  | .malformed .. | .rejected .. => "refused"
  | .unsupported .. => "unsupported"
  | .setupOnly .. => "setup"
  | .proofs setup proof remaining =>
      if remaining = 0 ∧ 0 < setup + proof then "success" else "incomplete"

private def diagnostic : Verdict → Option String
  | .malformed _ .truncatedInteger => some "File terminated too soon"
  | .malformed _ (.unknownOpcode code) => some s!"Unexpected opCode: {code}"
  | .rejected _ _ (.missing space) =>
      some ("No " ++ (match space with
        | .symbol => "symbol" | .term => "term" | .theorem => "theorem"
        | .challenge => "challenge") ++ " at position")
  | .rejected _ _ (.occupied .theorem) => some "Placing a theorem on an already existing theorem"
  | .rejected _ _ (.inferenceInSetup .instantiate) =>
      some "Inference rules (instantiate) should not run in challenge stage."
  | .rejected _ _ .theoremFailed => some "theorem derivation failed"
  | .rejected _ _ .challengeMismatch => some "Given theorem doesn't match the challenge"
  | _ => none

private def challenges : Verdict → Json
  | .proofs setup proof remaining => Json.mkObj [
      ("setup", toJson setup), ("proof", toJson proof), ("remaining", toJson remaining)]
  | _ => .null

def main (arguments : List String) : IO UInt32 := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  let root : System.FilePath := directory
  IO.FS.createDirAll root
  let mut manifest : Array Json := #[]
  for entry in caseTable ++ Mettapedia.Languages.VibeITP.Native.ProtocolV2LogicalControls.completionCases do
    let mut setupNames : Array Json := #[]
    let mut proofNames : Array Json := #[]
    for (bytes, index) in entry.setupFiles.zipIdx do
      let name := s!"{entry.name}-setup-{index}.lgc"
      IO.FS.writeBinFile (root / name) ⟨bytes.toArray⟩
      setupNames := setupNames.push (toJson name)
    for (bytes, index) in entry.proofFiles.zipIdx do
      let name := s!"{entry.name}-proof-{index}.pfc"
      IO.FS.writeBinFile (root / name) ⟨bytes.toArray⟩
      proofNames := proofNames.push (toJson name)
    let actual := ProtocolV2.checkRun entry.setupFiles entry.proofFiles
    unless actual = entry.expected do
      throw (IO.userError s!"reference control failed: {entry.name}")
    manifest := manifest.push (Json.mkObj [
      ("name", toJson entry.name), ("setup", .arr setupNames), ("proofs", .arr proofNames),
      ("expected", toJson (resultClass entry.expected)), ("diagnostic", toJson (diagnostic entry.expected)),
      ("challenges", challenges entry.expected),
      ("leanVerdict", toJson (reprStr actual))])
  IO.FS.writeFile (root / "manifest.json") (Json.arr manifest |>.pretty)
  return 0
