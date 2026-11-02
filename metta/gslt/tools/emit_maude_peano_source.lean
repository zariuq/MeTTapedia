import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSourceLowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeLinkedPeanoEmission
import Mettapedia.Languages.Maude.PeanoNormalization
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-! Select the existing certified Peano realizer only after independently
elaborating the complete source module and checking its full IR against the
realizer's theory. Declaration IDs are allocated through an explicit symbol
table; source terms and equation bodies are never obtained from that table.
The link returns a checked structural equality witness. Universal source
elaboration remains a separate correctness obligation.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.OSLF.MeTTaIL

def main (arguments : List String) : IO Unit := do
  let [sourcePath, packetPath, directory, moduleName] := arguments
    | throw (IO.userError "expected source, retained parser packets, output and selected module")
  let output := System.FilePath.mk directory
  if ← output.pathExists then throw (IO.userError "output already exists")
  let .ok packets := SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "malformed parser-result packets")
  let trees ← packets.mapM fun
    | .expression [.symbol "result", tree, .symbol "nil"] => pure tree
    | _ => throw (IO.userError "expected retained whole-input result packets")
  let names : MaudeSourceLowering.Names := {
    operators := Maude.Examples.peano.signature.operators.map MaudeSourceLowering.OperatorBinding.ofOperator
    equations := Maude.Examples.peano.equations.map (·.name) }
  let settings : MaudeSourceLowering.Settings := {names := [(moduleName, names)]}
  let input ← IO.FS.readFile sourcePath
  let meanings := trees.filterMap fun tree =>
    (GoldCoreSourceLowering.maude input tree settings).toOption.map (·.lowered)
  let first :: rest := meanings | throw (IO.userError "source elaboration refused")
  unless rest.all (fun other => decide (other = first)) do
    throw (IO.userError "retained source alternatives have different meanings")
  let some selected := first.modules.find? (·.theory.name == moduleName)
    | throw (IO.userError "selected source module is absent")
  let .ok actual := selected.closedTheory | throw (IO.userError "imported theories require certificates")
  let some _ := Maude.SchemaLink.check actual Maude.Examples.peano
    | throw (IO.userError "elaborated IR does not match the certified Peano theory")
  let [query] := first.commands.filter (·.moduleName == moduleName)
    | throw (IO.userError "expected one source command for the selected module")
  unless query.kind == .reduce do throw (IO.userError "this realizer handles the reduce command")
  let context := query.context.filter (fun declaration => query.source.variables.contains declaration.1)
  let spec := MaudeCompilation.NormalizationStage.PeanoEmission.spec context
  let plan := spec.plan
  let emitted ← match CompleteEmission.emitText? spec "maude-source" .classes with
    | .ok emitted => pure emitted
    | .error _ => throw (IO.userError "certified Peano realizer emission refused")
  let encode := fun term => CettaWire.Term.render (InferenceCettaWire.encodePattern (MaudeCompilation.encode term))
  let source := encode query.source
  let expected := encode (Maude.PeanoNormalization.reduce query.source)
  let planWire := CettaWire.Term.render (CompletePlanWire.planTerm plan plan.snapshot.freeTypes [] (.base "Nat"))
  let standard := CettaWire.Term.render (StandardWire.commitTerm plan .canonical (CompleteEmission.table spec))
  let controls :=
    "!(let* (($plan (quote " ++ planWire ++ ")) ($standard (quote " ++ standard ++ "))" ++
    " ($source (quote " ++ source ++ ")) ($expected (quote " ++ expected ++ "))" ++
    " ($begun (maude-source:begin $source))" ++
    " ($direct (gslt:runner:advance ClassSearch $plan $standard 4000 20 $begun))" ++
    " ($first (gslt:runner:advance ClassSearch $plan $standard 17 20 $begun))" ++
    " ($resumed (gslt:runner:advance ClassSearch $plan $standard 3983 20 $first)))" ++
    " (case $direct (((ClassMachine $phase $state $search $states $receipts)" ++
    " (println! (MaudeSourceNativeControl (== $phase ClassDone)" ++
    " (== $state $expected) (== $direct $resumed)))))))\n"
  let .ok parsed := SpaceSemantics.readProgram controls | throw (IO.userError "generated command is malformed")
  unless parsed.initializers.length == 1 do throw (IO.userError "generated command was not retained")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") controls
  IO.FS.writeFile (output / "scope.json") (Lean.Json.mkObj [
    ("scope", .str "source Peano IR checked against the certified schema; shared realizer"),
    ("retainedTrees", Lean.toJson trees.length), ("validElaborations", Lean.toJson meanings.length),
    ("sourceModule", .str moduleName), ("expectedNatural", Lean.toJson (Maude.PeanoNormalization.numeralValue?
      (Maude.PeanoNormalization.reduce query.source))),
    ("backendAgreementTheorem", .str "MaudeCompilation.NormalizationStage.LinkedPeano.emitted_source_run"),
    ("universalFrontendCorrespondence", .bool false), ("linkReflectionProved", .bool true),
    ("fullM0Qualified", .bool false)]).pretty
  IO.println "emitted independently elaborated source through the Peano realizer"
