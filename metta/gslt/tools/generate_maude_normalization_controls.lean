import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeNormalizationOSLFControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoEmissionAgreement
import Mettapedia.Languages.Maude.PeanoNormalization
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! Emit the oriented Peano-equation stage through the shared compiler.
These controls compare the stage with the source reducer. Complete M0
normalization certificates and source/native adequacy are separate checks. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def generate (directory label : String) : IO Unit := do
  let entry : Maude.Term × Maude.VariableContext ← match label with
    | "add23" => pure (Maude.Examples.binary "peano.add" (Maude.Examples.numeral "peano" 2) (Maude.Examples.numeral "peano" 3), [])
    | "mul23" => pure (Maude.Examples.binary "peano.mul" (Maude.Examples.numeral "peano" 2) (Maude.Examples.numeral "peano" 3), [])
    | "zero" => pure (Maude.Examples.numeral "peano" 0, [])
    | "open" => pure (Maude.Examples.binary "peano.add" (Maude.Examples.numeral "peano" 0) (.var "N"), [("N", "Nat")])
    | "open-stuck" => pure (Maude.Examples.binary "peano.add" (.var "N") (Maude.Examples.numeral "peano" 0), [("N", "Nat")])
    | _ => throw (IO.userError "expected add23, mul23, zero, open or open-stuck")
  let source := entry.1
  let expected := Maude.PeanoNormalization.reduce source
  let spec := NormalizationStage.PeanoEmission.spec entry.2
  let plan := spec.plan
  let .ok emitted := CompleteEmission.emitText? spec "maude-normalization" .classes
    | throw (IO.userError s!"normalization-stage emission refused: {reprStr plan.obligations}")
  let render := fun term => CettaWire.Term.render (InferenceCettaWire.encodePattern (encode term))
  let planWire := CettaWire.Term.render (CompletePlanWire.planTerm plan plan.snapshot.freeTypes [] (.base "Nat"))
  let standard := CettaWire.Term.render (StandardWire.commitTerm plan .canonical (CompleteEmission.table spec))
  let controls :=
    "(: m0-test:plan (-> %Undefined%))\n(= (m0-test:plan) (quote " ++ planWire ++ "))\n" ++
    "(: m0-test:standard (-> %Undefined%))\n(= (m0-test:standard) (quote " ++ standard ++ "))\n" ++
    "!(println! (MaudeNormalizationStart " ++ reprStr label ++ "))\n" ++
    "!(let* (($plan (m0-test:plan)) ($standard (m0-test:standard))" ++
    " ($source (quote " ++ render source ++ "))" ++
    " ($expected (quote " ++ render expected ++ "))" ++
    " ($begun (maude-normalization:begin $source))" ++
    " ($direct (gslt:runner:advance ClassSearch $plan $standard 4000 20 $begun))" ++
    " ($first (gslt:runner:advance ClassSearch $plan $standard 17 20 $begun))" ++
    " ($resumed (gslt:runner:advance ClassSearch $plan $standard 3983 20 $first)))" ++
    " (case $direct (((ClassMachine $phase $state $search $states $receipts)" ++
    " (println! (MaudeNormalizationControl " ++ reprStr label ++
    " (== $phase ClassDone) (== $state $expected) (== $direct $resumed)" ++
    " (gslt:automata:length $states) (gslt:automata:length $receipts)))))))\n"
  let output := System.FilePath.mk directory
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") controls
  IO.FS.writeFile (output / "scope.json") (Lean.Json.mkObj [
    ("program", .str label), ("stage", .str "oriented Peano equations through the shared GSLT runner"),
    ("expectedNatural", Lean.toJson (Maude.PeanoNormalization.numeralValue? expected)),
    ("expectedVariableN", .bool (expected == .var "N")), ("expectedUnchanged", .bool (expected == source)),
    ("oslfReachesExpected", Lean.toJson (NormalizationStage.OSLFControls.reaches source expected)),
    ("oslfWrongOneStep", Lean.toJson (NormalizationStage.OSLFControls.wrongOneStep source)),
    ("oslfFuel", .num 16), ("oslfRounds", .num 16),
    ("sourceAgreementTheorem", .str "NormalizationStage.PeanoEmission.emitted_source_run"),
    ("fullMaudeQualified", .bool false), ("normalizationCertificatesComplete", .bool false)]).pretty
  IO.println s!"emitted {label} normalization-stage control"

def main (arguments : List String) : IO Unit := do
  match arguments with
  | [directory, label] => generate directory label
  | _ => throw (IO.userError "expected an output directory and program label")
