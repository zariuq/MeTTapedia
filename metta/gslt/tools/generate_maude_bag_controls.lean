import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUEquationCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering
import Mettapedia.Languages.Maude.BagCardinality
import Mettapedia.Languages.Maude.BagIdempotence
import Mettapedia.Languages.Maude.SchemaLink
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner

/-! Ordinary GOLD-BAG source through the shared ACU equation stage. Typed
context traversal handles nested cardinality calls; the tests do not grant
a generic Maude normalization certificate.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace MaudeBagControls

open Mettapedia.Languages
open Maude.BagCardinality
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open MaudeCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

inductive Kind where
  | cardinality | idempotence

def Kind.theory : Kind → Maude.Theory
  | .cardinality => Maude.Examples.cardinality
  | .idempotence => Maude.Examples.idempotent

def Kind.operation (kind : Kind) : Maude.ACUOperation kind.theory [] :=
  match kind with
  | .cardinality => Maude.BagCardinality.operation
  | .idempotence => Maude.BagIdempotence.operation

def Kind.sort : Kind → String
  | .cardinality => "Nat"
  | .idempotence => "Bag"

def Kind.expected? (kind : Kind) (source : Maude.Term) : Option Maude.Term :=
  match kind with
  | .cardinality => numeral <$> Maude.BagCardinality.value? source
  | .idempotence => some (Maude.BagIdempotence.operation.fold (Maude.BagIdempotence.operation.flatten source).dedup)

def sourceModule (kind : Kind) (sourcePath packetPath : String) : IO (Maude.Theory × Maude.Term) := do
  let input ← IO.FS.readFile sourcePath
  let .ok packets := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "malformed retained parser packets")
  let trees ← packets.mapM fun
    | .expression [.symbol "result", tree, .symbol "nil"] => pure tree
    | _ => throw (IO.userError "expected complete retained parser results")
  let names : List (String × MaudeSourceLowering.Names) :=
    [Maude.Examples.cardinality, Maude.Examples.idempotent].map fun theory =>
      let entry : MaudeSourceLowering.Names := {
        operators := theory.signature.operators.map MaudeSourceLowering.OperatorBinding.ofOperator
        equations := theory.equations.map (·.name) }
      (theory.name, entry)
  let settings : MaudeSourceLowering.Settings := {names := names}
  let meanings := trees.filterMap fun tree => (MaudeSourceLowering.lower input tree settings).toOption
  let first :: rest := meanings | throw (IO.userError "source elaboration refused")
  unless rest.all (fun other => decide (other = first)) do throw (IO.userError "source alternatives disagree")
  let some selected := first.modules.find? (·.theory.name == kind.theory.name)
    | throw (IO.userError "selected source module is absent")
  let .ok theory := selected.closedTheory | throw (IO.userError "source imports require certificates")
  let [query] := first.commands.filter (·.moduleName == kind.theory.name)
    | throw (IO.userError "expected one selected source command")
  unless query.kind == .reduce && query.source.variables.isEmpty do
    throw (IO.userError "this control expects a ground reduction command")
  pure (theory, query.source)

def referenceTerm? : Maude.Term → Option String
  | .app "bag.zero" [] => some "0"
  | .app "bag.succ" [source] => do pure ("s(" ++ (← referenceTerm? source) ++ ")")
  | .app "bag.card" [source] => do pure ("card(" ++ (← referenceTerm? source) ++ ")")
  | .app "bag.merge" [left, right] => do pure ("(" ++ (← referenceTerm? left) ++ " " ++ (← referenceTerm? right) ++ ")")
  | .app "set.merge" [left, right] => do pure ("(" ++ (← referenceTerm? left) ++ " " ++ (← referenceTerm? right) ++ ")")
  | .app "bag.empty" [] => some "empty"
  | .app "bag.a" [] => some "a"
  | .app "bag.b" [] => some "b"
  | .app "set.empty" [] => some "empty"
  | .app "set.a" [] => some "a"
  | .app "set.b" [] => some "b"
  | _ => none

structure Control where
  label : String
  source : Maude.Term

def cardinalityControls (source : Maude.Term) : List Control :=
  [⟨"source-standard", source⟩,
   ⟨"empty", card operation.unit⟩,
   ⟨"duplicates", card (operation.fold [token "a", token "a"])⟩,
   ⟨"nested-successor", successor (card (operation.fold [token "a", token "b"]))⟩,
   ⟨"identity", card (operation.merge operation.unit (operation.merge (token "a") operation.unit))⟩,
   ⟨"mixed-bag", card (operation.fold [token "b", token "a", token "b", token "b"])⟩,
   ⟨"constructor-normal", successor (successor (numeral 0))⟩]

def idempotenceControls (source : Maude.Term) : List Control :=
  let operation := Maude.BagIdempotence.operation
  let a := Maude.Term.app "set.a" []
  let b := Maude.Term.app "set.b" []
  [⟨"source-standard", source⟩, ⟨"empty", operation.unit⟩, ⟨"single", a⟩,
   ⟨"duplicates", operation.fold [a, a]⟩, ⟨"all-same", operation.fold [a, a, a, a]⟩,
   ⟨"mixed-bag", operation.fold [b, a, b, b]⟩, ⟨"distinct", operation.fold [a, b]⟩,
   ⟨"identity", operation.merge operation.unit (operation.merge a operation.unit)⟩]

def controls (kind : Kind) (source : Maude.Term) : List Control :=
  match kind with
  | .cardinality => cardinalityControls source
  | .idempotence => idempotenceControls source

def main (arguments : List String) : IO Unit := do
  let (directory, sourcePath, packetPath, kind) ← match arguments with
    | [directory, sourcePath, packetPath] => pure (directory, sourcePath, packetPath, Kind.cardinality)
    | [directory, sourcePath, packetPath, "GOLD-BAG"] => pure (directory, sourcePath, packetPath, Kind.cardinality)
    | [directory, sourcePath, packetPath, "GOLD-SET"] => pure (directory, sourcePath, packetPath, Kind.idempotence)
    | _ => throw (IO.userError "expected output, source, retained packets and optionally GOLD-BAG or GOLD-SET")
  let output := System.FilePath.mk directory
  if ← output.pathExists then throw (IO.userError "output already exists")
  let stdout ← IO.getStdout
  stdout.putStrLn "elaborating ordinary bag source"
  stdout.flush
  let (actual, source) ← sourceModule kind sourcePath packetPath
  let some witness := Maude.SchemaLink.check actual kind.theory
    | throw (IO.userError "source rows differ from the checked equation schema")
  have signatureSame : actual.signature = kind.theory.signature := by
    simpa only [Maude.Theory.named] using congrArg Maude.Theory.signature witness.same
  let operation := kind.operation
  let actualOperation : Maude.ACUOperation actual [] := {
    declaration := operation.declaration
    declared := by rw [signatureSame]; exact operation.declared
    arguments := operation.arguments
    associative := operation.associative
    commutative := operation.commutative
    unit := operation.unit
    identity := operation.identity
    unit_sorted := by rw [signatureSame]; exact operation.unit_sorted }
  let .ok prepared := (match kind with
      | .cardinality => ACUEquationCompilation.prepare actualOperation
      | .idempotence => ACUEquationCompilation.prepareIdempotence actualOperation)
    | throw (IO.userError "source equation compilation refused")
  let spec : CompleteEmission.Spec := ⟨ACUEquationCompilation.plan prepared, [], .base kind.sort, .canonical⟩
  stdout.putStrLn s!"checking context plan: {reprStr spec.plan.obligations}"
  stdout.flush
  unless (CompleteEmission.pendingFor spec .classes).isEmpty do
    throw (IO.userError "shared context plan has pending obligations")
  let .ok emitted := CompleteEmission.emitText? spec "maude-bag" .classes
    | throw (IO.userError "shared emission refused the bag equation stage")
  let search := Complete.Normalized.search spec.plan [] (.base kind.sort) .canonical
  let planWire := (CompletePlanWire.planTerm spec.plan [] [] (.base kind.sort)).render
  let standardWire := (StandardWire.commitTerm spec.plan .canonical (CompleteEmission.table spec)).render
  let mut lines := []
  let mut references : List Lean.Json := []
  for control in controls kind source do
    stdout.putStrLn ("starting model " ++ control.label)
    stdout.flush
    let some input := ACUEquationCompilation.term? actualOperation [] control.source
      | throw (IO.userError "a control source failed typed physical lowering")
    let some expectedSource := kind.expected? control.source
      | throw (IO.userError "a control source has no independent expected value")
    let some expectedPhysical := ACUEquationCompilation.term? actualOperation [] expectedSource
      | throw (IO.userError "an expected value failed typed physical lowering")
    let expected := Complete.Normalized.commit spec.plan .canonical expectedPhysical
    let begun := Mettapedia.Machines.ResumableSearchRunner.Machine.begin search
      (Complete.Normalized.commit spec.plan .canonical input)
    let direct := Mettapedia.Machines.ResumableSearchRunner.Machine.advance search 50 3000 begun
    unless direct.phase == .done && direct.state == expected do
      throw (IO.userError s!"{control.label}: model did not complete with its independent expected value")
    let model := (CompleteExecution.classMachineTerm spec.plan direct).render
    let sourceWire := CettaWire.Term.render (InferenceCettaWire.encodePattern input)
    let expectedWire := CettaWire.Term.render (InferenceCettaWire.encodePattern expected)
    lines := lines ++ ["!(let* (($plan (quote " ++ planWire ++ ")) ($standard (quote " ++ standardWire ++ "))" ++
      " ($source (quote " ++ sourceWire ++ ")) ($expected (quote " ++ expectedWire ++ ")) ($model (quote " ++ model ++ "))" ++
      " ($begun (maude-bag:begin $source)) ($direct (gslt:runner:advance ClassSearch $plan $standard 50 3000 $begun))" ++
      " ($first (gslt:runner:advance ClassSearch $plan $standard 2 3000 $begun))" ++
      " ($resumed (gslt:runner:advance ClassSearch $plan $standard 48 3000 $first)))" ++
      " (case $direct (((ClassMachine $phase $state $pending $states $receipts)" ++
      " (println! (MaudeBagNativeControl " ++ reprStr control.label ++
      " (== $phase ClassDone) (== $state $expected) (== $direct $resumed) (== $direct $model)))))))\n"]
    let some reference := referenceTerm? control.source | throw (IO.userError "a reference control is outside its renderer")
    let expectedObservation ← match kind with
      | .cardinality =>
        let some value := Maude.BagCardinality.value? control.source | throw (IO.userError "missing source value")
        pure (Lean.toJson value)
      | .idempotence =>
        let names ← (operation.flatten expectedSource).mapM fun part => do
          let some spelling := referenceTerm? part | throw (IO.userError "missing source token spelling")
          pure spelling
        pure (Lean.toJson names)
    references := references ++ [Lean.Json.mkObj [("label", .str control.label), ("term", .str reference),
      ("expected", expectedObservation)]]
  let text := String.join lines
  let .ok parsed := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readProgram text
    | throw (IO.userError "generated controls are malformed")
  unless parsed.initializers.length == (controls kind source).length do throw (IO.userError "a control was lost")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") text
  IO.FS.writeFile (output / "reference-cases.json") (Lean.toJson references).pretty
  IO.FS.writeFile (output / "scope.json") (Lean.Json.mkObj [
    ("scope", .str "ordinary source through an ACU equation stage and typed context traversal"),
    ("sourceModule", .str kind.theory.name), ("resultSort", .str kind.sort),
    ("moduleCertificatesComplete", .bool false), ("fullM0Qualified", .bool false)]).pretty

end MaudeBagControls

def main := MaudeBagControls.main
