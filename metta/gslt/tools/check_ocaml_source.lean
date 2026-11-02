import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
import Mettapedia.Languages.OCaml.Examples
import Mettapedia.Languages.OCaml.ObservationChecking
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Replay one explicitly selected native parser result into the OCaml arena
and compare its observation with an independent standard-example fixture.
This checks source lowering and the reference machine, not emitted MeTTa.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.OCaml
open Mettapedia.Languages.MeTTa.PeTTa

def expected? (label : String) : Option Result :=
  match label with
  | "simultaneous_binding" => some (.ok (.tuple [Examples.integer 1, Examples.integer 10]))
  | "constructor_fields" => some (.ok (.tuple [Examples.integer 5, Examples.integer (-5)]))
  | "constructor_capture" => some (.ok (Examples.integer 1))
  | "minimum_integer" => some (.ok (Examples.integer (-4611686018427387904)))
  | "minimum_negation" => some (.ok (.tuple [Examples.integer (-4611686018427387904), Examples.integer (-4611686018427387904)]))
  | "recursive_lambda_value" => some (.ok (Examples.integer 5))
  | _ => (Examples.examples.find? (·.name == label)).map (·.expected)

def main (arguments : List String) : IO Unit := do
  let [sourcePath, packetPath, label] := arguments
    | throw (IO.userError "expected source, selected parser packet and example name")
  let .ok [.expression [.symbol "result", tree, .symbol "nil"]] :=
      SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "expected exactly one explicitly selected whole-input result")
  let lowered := OCamlSourceLowering.lower (← IO.FS.readFile sourcePath) tree
  if label == "--refuse" then
    match lowered with
    | .error _ => IO.println "(OCamlSourceRefusal true)"; return
    | .ok _ => throw (IO.userError "unexpected frontend acceptance")
  let program ← match lowered with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let some expected := expected? label
    | throw (IO.userError "unknown independent observation fixture")
  let direct := run program 20000 (begin program)
  let some _evaluation := checkedObservation program 20000 expected
    | throw (IO.userError s!"source observation differs: {reprStr direct}")
  unless resume program 19983 (run program 17 (begin program)) == direct do
    throw (IO.userError "interrupted source execution differs from direct execution")
  IO.println s!"(OCamlSourceControl {reprStr label} true true {program.code.size})"
