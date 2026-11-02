import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUStagePair
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUQueryController
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering
import Mettapedia.Languages.Maude.MutexNormalization
import Mettapedia.Languages.Maude.SchemaLink
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.OSLF.MeTTaIL.Complete.Settled

/-! Compose source E normalization, an explicit R reduct, and source query
matching for the standard mutex program. The shared stages remain distinct;
the controls do not grant a generic E/R coherence certificate.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace MaudeMutexControls

open Mettapedia.Languages
open Maude.MutexNormalization
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open MaudeCompilation
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def sourceModule (sourcePath packetPath : String) : IO (Maude.Theory × Maude.Term × Maude.Term) := do
  let input ← IO.FS.readFile sourcePath
  let .ok packets := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "malformed retained parser packets")
  let trees ← packets.mapM fun
    | .expression [.symbol "result", tree, .symbol "nil"] => pure tree
    | _ => throw (IO.userError "expected complete retained parser results")
  let names : MaudeSourceLowering.Names := {
    operators := Maude.Examples.mutex.signature.operators.map MaudeSourceLowering.OperatorBinding.ofOperator
    equations := Maude.Examples.mutex.equations.map (·.name)
    rules := Maude.Examples.mutex.rules.map (·.name) }
  let settings : MaudeSourceLowering.Settings := {names := [("GOLD-MUTEX", names)]}
  let meanings := trees.filterMap fun tree => (MaudeSourceLowering.lower input tree settings).toOption
  let first :: rest := meanings | throw (IO.userError "source elaboration refused")
  unless rest.all (fun other => decide (other = first)) do throw (IO.userError "source alternatives disagree")
  let [selected] := first.modules | throw (IO.userError "expected one source module")
  let .ok theory := selected.closedTheory | throw (IO.userError "source imports require certificates")
  let [query] := first.commands | throw (IO.userError "expected one source command")
  unless query.kind == .searchStar && query.conditions.isEmpty && query.source.variables.isEmpty do
    throw (IO.userError "this profile expects an unconditional search from a ground marking")
  let some target := query.target | throw (IO.userError "the source target is missing")
  pure (theory, query.source, target)

def referenceTerm? : Maude.Term → Option String
  | .app "mutex.merge" [left, right] => do pure ("(" ++ (← referenceTerm? left) ++ " " ++ (← referenceTerm? right) ++ ")")
  | .app label [] =>
    if label.startsWith "mutex." then some (label.drop 6 |>.toString) else none
  | _ => none

structure Control where
  label : String
  source : Maude.Term

def controls (source : Maude.Term) : List Control :=
  [⟨"source-standard", source⟩, ⟨"expanded", expanded⟩,
   ⟨"residual-resource", operation.merge initial (token "idle1")⟩,
   ⟨"unsafe-extra-permit", operation.merge initial (token "permit")⟩]

def main (arguments : List String) : IO Unit := do
  let [directory, sourcePath, packetPath] := arguments | throw (IO.userError "expected output, source and retained packets")
  let output := System.FilePath.mk directory
  if ← output.pathExists then throw (IO.userError "output already exists")
  let stdout ← IO.getStdout
  stdout.putStrLn "elaborating ordinary mutex source"
  stdout.flush
  let (actual, source, target) ← sourceModule sourcePath packetPath
  let some witness := Maude.SchemaLink.check actual Maude.Examples.mutex
    | throw (IO.userError "source rows differ from the checked mutex schema")
  have signatureSame : actual.signature = Maude.Examples.mutex.signature := by
    simpa only [Maude.Theory.named] using congrArg Maude.Theory.signature witness.same
  let actualOperation : Maude.ACUOperation actual [] := {
    declaration := operation.declaration
    declared := by rw [signatureSame]; exact operation.declared
    arguments := operation.arguments
    associative := operation.associative
    commutative := operation.commutative
    unit := operation.unit
    identity := operation.identity
    unit_sorted := by rw [signatureSame]; exact operation.unit_sorted }
  let .ok stages := ACUStagePair.prepare actualOperation | throw (IO.userError "source E/R stage construction refused")
  let eSpec : CompleteEmission.Spec := ⟨ACUEquationCompilation.plan stages.equations, [], .base "Marking", .canonical⟩
  let rSpec : CompleteEmission.Spec := ⟨ACUBagCompilation.plan stages.transitions, [], .base "Marking", .canonical⟩
  let .ok query := ACUBagQuery.prepare actualOperation stages.transitions target
    | throw (IO.userError "source query compilation refused")
  let qSpec : CompleteEmission.Spec := ⟨ACUBagCompilation.plan query.language, [], .base ACUBagQuery.stateSort, .canonical⟩
  let eSearch := Complete.Normalized.search eSpec.plan [] (.base "Marking") .canonical
  let rSearch := Complete.Normalized.search rSpec.plan [] (.base "Marking") .canonical
  let qWrapper := ACUBagCompilation.wrapperName operation.declaration
  let mut emitted := ""
  for (name, spec) in [("mutex-e", eSpec), ("mutex-r", rSpec), ("mutex-q", qSpec)] do
    unless (CompleteEmission.pendingFor spec .classes).isEmpty do
      throw (IO.userError s!"{name}: shared stage has pending obligations")
    let .ok text := CompleteEmission.emitText? spec name .classes | throw (IO.userError "shared stage emission refused")
    emitted := emitted ++ text ++ "\n"
  let plan := fun spec => (CompletePlanWire.planTerm spec.plan [] spec.bound spec.expected).render
  let standard := fun spec => (StandardWire.commitTerm spec.plan .canonical (CompleteEmission.table spec)).render
  let wire := fun value => CettaWire.Term.render (InferenceCettaWire.encodePattern value)
  let mut lines := []
  let mut references : List Lean.Json := []
  for control in controls source do
    stdout.putStrLn ("starting model " ++ control.label)
    stdout.flush
    let some input := ACUEquationCompilation.term? actualOperation [] control.source
      | throw (IO.userError "source marking failed physical lowering")
    let eBegun := Mettapedia.Machines.ResumableSearchRunner.Machine.begin eSearch
      (Complete.Normalized.commit eSpec.plan .canonical input)
    let eDone := Mettapedia.Machines.ResumableSearchRunner.Machine.advance eSearch 10 3000 eBegun
    unless eDone.phase == .done do throw (IO.userError "initial equation normalization remains pending")
    let explorer := Complete.Settled.roundsUntilSettled rSearch 5000
      (Complete.Explore.begin rSearch (Complete.Normalized.commit rSpec.plan .canonical eDone.state))
    unless Complete.Settled.settled rSearch explorer do throw (IO.userError "transition graph remains pending")
    let states := explorer.nodes.map (·.state)
    let qDone := ACUBagQuery.Controller.advance qSpec qWrapper 128 3000 (ACUBagQuery.Controller.begin qSpec states)
    let .done answers := qDone | throw (IO.userError "query matching remains pending")
    if control.label == "source-standard" && (!answers.isEmpty || states.length != 3) then
      throw (IO.userError "standard mutex safety boundary disagrees")
    if control.label == "unsafe-extra-permit" && answers.isEmpty then
      throw (IO.userError "unsafe extra-permit control failed to expose the counterexample")
    let tokenNames := fun (value : Pattern) => do
      let .apply wrapper [.collection .hashBag parts none] := value
        | throw (IO.userError "an explored marking lost its bag carrier")
      unless wrapper == qWrapper do throw (IO.userError "a marking has a foreign wrapper")
      parts.mapM fun part => do
        let some term := MaudeCompilation.decode? part | throw (IO.userError "a marking has no source readback")
        let some name := referenceTerm? term | throw (IO.userError "a source token has no spelling")
        pure name
    let reachable ← states.mapM tokenNames
    let substitutions ← answers.mapM tokenNames
    let some sourceText := referenceTerm? control.source | throw (IO.userError "source reference rendering refused")
    references := references ++ [Lean.Json.mkObj [("label", .str control.label), ("source", .str sourceText),
      ("reachable", Lean.toJson reachable), ("solutions", Lean.toJson substitutions)]]
    let expectedStates := (encodeList InferenceCettaWire.encodePattern states).render
    let expectedAnswers := (encodeList InferenceCettaWire.encodePattern answers).render
    let expectedE := (CompleteExecution.classMachineTerm eSpec.plan eDone).render
    lines := lines ++ ["!(let* (($ep (quote " ++ plan eSpec ++ ")) ($es (quote " ++ standard eSpec ++ "))" ++
      " ($rp (quote " ++ plan rSpec ++ ")) ($rs (quote " ++ standard rSpec ++ "))" ++
      " ($qp (quote " ++ plan qSpec ++ ")) ($qs (quote " ++ standard qSpec ++ "))" ++
      " ($input (quote " ++ wire input ++ ")) ($expected-e (quote " ++ expectedE ++ "))" ++
      " ($expected-states (quote " ++ expectedStates ++ ")) ($expected-answers (quote " ++ expectedAnswers ++ "))" ++
      " ($begun (mutex-e:begin $input)) ($edone (gslt:runner:advance ClassSearch $ep $es 10 3000 $begun))" ++
      " ($e-first (gslt:runner:advance ClassSearch $ep $es 1 3000 $begun))" ++
      " ($e-resumed (gslt:runner:advance ClassSearch $ep $es 9 3000 $e-first)))" ++
      " (case $edone (((ClassMachine $phase $state $pending $history $receipts)" ++
      " (let* (($states (mutex-r:explore $state 5000))" ++
      " ($answers (gslt:maude-query:filter $qp $qs " ++ (CettaWire.Term.string ACUBagQuery.requestName).render ++ " " ++
      (CettaWire.Term.string ACUBagQuery.resultName).render ++ " " ++ (CettaWire.Term.string qWrapper).render ++ " $states LNil 128 3000)))" ++
      " (println! (MaudeMutexNativeControl " ++ reprStr control.label ++
      " (== $phase ClassDone) (== $edone $expected-e) (== $edone $e-resumed)" ++
      " (== $states $expected-states) (== $answers $expected-answers))))))))\n"]
  let text := String.join lines
  let .ok parsed := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readProgram text
    | throw (IO.userError "generated controls are malformed")
  unless parsed.initializers.length == (controls source).length do throw (IO.userError "a control was lost")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") emitted
  IO.FS.writeFile (output / "controls.metta") text
  IO.FS.writeFile (output / "reference-cases.json") (Lean.toJson references).pretty
  IO.FS.writeFile (output / "scope.json") (Lean.Json.mkObj [
    ("scope", .str "source E initialization, primitive R exploration, authored target matching"),
    ("fullCoherenceCertificate", .bool false), ("fullM0Qualified", .bool false)]).pretty

end MaudeMutexControls

def main := MaudeMutexControls.main
