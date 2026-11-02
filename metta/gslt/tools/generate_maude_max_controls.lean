import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeConditionalImport
import Mettapedia.Languages.Maude.ConditionalMaxBounds
import Mettapedia.Languages.Maude.ConditionalMaxValue
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner

/-! Conditional equations execute through the shared finite premise
provider. Bounds are computed from each input. The optional source route
checks the retained source schema and the proved ground BOOL import profile.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace MaudeMaxControls

open Mettapedia.Languages
open Maude.ConditionalMax
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

structure Control where
  label : String
  source : Maude.Term

def controls : List Control :=
  [⟨"source-standard-ir", maximum (numeral 2) (numeral 1)⟩,
   ⟨"right-larger", maximum (numeral 1) (numeral 3)⟩,
   ⟨"equal", maximum (numeral 2) (numeral 2)⟩,
   ⟨"zero", maximum (numeral 0) (numeral 0)⟩,
   ⟨"nested-max", maximum (maximum (numeral 1) (numeral 2)) (numeral 3)⟩,
   ⟨"nested-successor", successor (maximum (numeral 1) (numeral 3))⟩,
   ⟨"constructor-normal", numeral 2⟩]

def referenceTerm? : Maude.Term → Option String
  | .app "max.zero" [] => some "0"
  | .app "max.succ" [source] => do pure ("s(" ++ (← referenceTerm? source) ++ ")")
  | .app "max.max" [left, right] => do pure ("max(" ++ (← referenceTerm? left) ++ "," ++ (← referenceTerm? right) ++ ")")
  | _ => none

def sourceModule (sourcePath packetPath : String) : IO (LanguageDef × Maude.Term) := do
  let input ← IO.FS.readFile sourcePath
  let .ok packets := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "malformed retained parser packets")
  let trees ← packets.mapM fun
    | .expression [.symbol "result", tree, .symbol "nil"] => pure tree
    | _ => throw (IO.userError "expected complete retained parser results")
  let meanings := trees.filterMap fun tree =>
    (MaudeSourceLowering.lower input tree MaudeConditionalImport.settings).toOption
  let first :: rest := meanings | throw (IO.userError "source elaboration refused")
  unless rest.all (fun other => decide (other = first)) do
    throw (IO.userError "source alternatives disagree")
  let [source] := first.modules | throw (IO.userError "expected one conditional module")
  let .ok language := MaudeConditionalImport.compile source
    | throw (IO.userError "source differs from the certified conditional BOOL import profile")
  let [query] := first.commands | throw (IO.userError "expected one conditional command")
  unless query.moduleName == source.theory.name && query.kind == .reduce &&
      query.sort == "Nat" && query.source.variables.isEmpty &&
      Maude.inferSort? source.theory.signature [] query.source == some query.sort &&
      query.target.isNone && query.conditions.isEmpty do
    throw (IO.userError "the conditional source profile expects a ground Nat reduction")
  pure (language, query.source)

def main (arguments : List String) : IO Unit := do
  let (directory, language, selectedControls, importedSource) ← match arguments with
    | [directory] => do
      let .ok language := ConditionalCompilation.prepare Maude.Examples.conditional
        | throw (IO.userError "conditional equation compilation refused")
      pure (directory, language, controls, false)
    | [directory, sourcePath, packetPath] => do
      let (language, source) ← sourceModule sourcePath packetPath
      pure (directory, language, ⟨"source-standard", source⟩ :: controls.drop 1, true)
    | _ => throw (IO.userError "expected output, optionally followed by ordinary source and retained packets")
  let output := System.FilePath.mk directory
  if ← output.pathExists then throw (IO.userError "output already exists")
  let stdout ← IO.getStdout
  let mut emitted := ""
  let mut lines := []
  let mut references : List Lean.Json := []
  for control in selectedControls do
    stdout.putStrLn ("starting model " ++ control.label)
    stdout.flush
    let bound := successorCount control.source
    let spec : CompleteEmission.Spec :=
      ⟨ConditionalCompilation.plan language bound, [], .base "Nat", .canonical⟩
    unless (CompleteEmission.pendingFor spec .classes).isEmpty do
      throw (IO.userError s!"conditional plan has pending obligations: {reprStr spec.plan.obligations}")
    let name := "maude-max-" ++ control.label
    let .ok text := CompleteEmission.emitText? spec name .classes
      | throw (IO.userError "shared conditional emission refused")
    emitted := emitted ++ text ++ "\n"
    let search := Complete.Normalized.search spec.plan [] (.base "Nat") .canonical
    let input := encode control.source
    let some value := value? control.source | throw (IO.userError "independent source value is unavailable")
    let expected := encode (numeral value)
    let begun := Mettapedia.Machines.ResumableSearchRunner.Machine.begin search input
    let direct := Mettapedia.Machines.ResumableSearchRunner.Machine.advance search 100 3000 begun
    unless direct.phase == .done && direct.state == expected do
      throw (IO.userError s!"{control.label}: model did not complete at its independent expected value")
    let planWire := (CompletePlanWire.planTerm spec.plan [] [] (.base "Nat")).render
    let standardWire := (StandardWire.commitTerm spec.plan .canonical (CompleteEmission.table spec)).render
    let wire := fun value => CettaWire.Term.render (InferenceCettaWire.encodePattern value)
    let model := (CompleteExecution.classMachineTerm spec.plan direct).render
    lines := lines ++ ["!(let* (($plan (quote " ++ planWire ++ ")) ($standard (quote " ++ standardWire ++ "))" ++
      " ($source (quote " ++ wire input ++ ")) ($expected (quote " ++ wire expected ++ ")) ($model (quote " ++ model ++ "))" ++
      " ($begun (" ++ name ++ ":begin $source)) ($direct (gslt:runner:advance ClassSearch $plan $standard 100 3000 $begun))" ++
      " ($first (gslt:runner:advance ClassSearch $plan $standard 2 3000 $begun))" ++
      " ($resumed (gslt:runner:advance ClassSearch $plan $standard 98 3000 $first)))" ++
      " (case $direct (((ClassMachine $phase $state $pending $states $receipts)" ++
      " (println! (MaudeMaxNativeControl " ++ reprStr control.label ++
      " (== $phase ClassDone) (== $state $expected) (== $direct $resumed) (== $direct $model)))))))\n"]
    let some reference := referenceTerm? control.source | throw (IO.userError "reference term is outside the fixed renderer")
    references := references ++ [Lean.Json.mkObj [("label", .str control.label), ("term", .str reference),
      ("expected", Lean.toJson value), ("bound", Lean.toJson bound),
      ("providerRows", Lean.toJson (ConditionalCompilation.provider bound).rows.length)]]
  let refusalSpec : CompleteEmission.Spec :=
    ⟨ConditionalCompilation.plan language 0, [], .base "Nat", .canonical⟩
  let refusalName := "maude-max-incomplete-envelope"
  let .ok refusalText := CompleteEmission.emitText? refusalSpec refusalName .classes
    | throw (IO.userError "negative guard stage emission refused")
  emitted := emitted ++ refusalText ++ "\n"
  let input := encode (maximum (numeral 2) (numeral 1))
  let search := Complete.Normalized.search refusalSpec.plan [] (.base "Nat") .canonical
  let begun := Mettapedia.Machines.ResumableSearchRunner.Machine.begin search input
  let direct := Mettapedia.Machines.ResumableSearchRunner.Machine.advance search 10 3000 begun
  unless direct.phase == .done && direct.state == input do
    throw (IO.userError "missing equality evidence incorrectly authorized a conditional reduction")
  let wire := fun value => CettaWire.Term.render (InferenceCettaWire.encodePattern value)
  lines := lines ++ ["!(let* (($source (quote " ++ wire input ++ ")) ($begun (" ++ refusalName ++ ":begin $source))" ++
    " ($plan (quote " ++ (CompletePlanWire.planTerm refusalSpec.plan [] [] (.base "Nat")).render ++ "))" ++
    " ($standard (quote " ++ (StandardWire.commitTerm refusalSpec.plan .canonical (CompleteEmission.table refusalSpec)).render ++ "))" ++
    " ($done (gslt:runner:advance ClassSearch $plan $standard 10 3000 $begun)))" ++
    " (case $done (((ClassMachine $phase $state $pending $states $receipts)" ++
    " (println! (MaudeMaxEnvelopeControl (== $phase ClassDone) (== $state $source)))))))\n"]
  let controlText := String.join lines
  let .ok parsed := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readProgram controlText
    | throw (IO.userError "generated controls are malformed")
  unless parsed.initializers.length == selectedControls.length + 1 do throw (IO.userError "a control was lost")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") controlText
  IO.FS.writeFile (output / "reference-cases.json") (Lean.toJson references).pretty
  IO.FS.writeFile (output / "scope.json") (Lean.Json.mkObj [
    ("scope", .str (if importedSource then
      "ordinary conditional source through the checked ground BOOL import profile and shared premise provider"
      else "conditional prepared IR through the shared finite premise provider")),
    ("originalBOOLImportAdmitted", .bool importedSource), ("universalGuardReflection", .bool false),
    ("fullM0Qualified", .bool false)]).pretty

end MaudeMaxControls

def main := MaudeMaxControls.main
