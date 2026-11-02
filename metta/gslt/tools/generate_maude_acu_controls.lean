import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUBagQuery
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUQueryController
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeSourceLowering
import Mettapedia.Languages.Maude.ACUFoldControls
import Mettapedia.Languages.Maude.SchemaLink
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.SearchWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassRunner
import Mettapedia.OSLF.MeTTaIL.Complete.Settled

/-! Exercise the actual ground ACU transition compiler through the shared
runner and explorer. These finite controls supplement source readback;
they do not assert full M0 qualification or general ACU completeness. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace MaudeACUControls

open Mettapedia.Languages
open Maude.ACUFoldControls
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def spec (language : LanguageDef) : CompleteEmission.Spec :=
  ⟨ACUBagCompilation.plan language, [], .base "Marking", .canonical⟩

def wrapper : String := ACUBagCompilation.wrapperName operation.declaration
def bag (parts : List Maude.Term) : Pattern := ACUBagPresentation.pack wrapper parts
def committed (language : LanguageDef) (state : Pattern) :=
  Complete.Normalized.commit (spec language).plan (spec language).mode state
def search (language : LanguageDef) :=
  Complete.Normalized.search (spec language).plan (spec language).bound (spec language).expected (spec language).mode
def begun (language : LanguageDef) (state : Pattern) :=
  Mettapedia.Machines.ResumableSearchRunner.Machine.begin (search language) (committed language state)
def advanced (language : LanguageDef) (state : Pattern) :=
  Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search language) 10 3000 (begun language state)
def explored (language : LanguageDef) (state : Pattern) (work : Nat) :=
  Complete.Explore.explore (search language) (committed language state) work

structure Control where
  label : String
  source : List Maude.Term
  result : List Maude.Term
  reachable : Option (List (List Maude.Term))
  work : Nat := 1000

def apple : Maude.Term := .app "vending.a" []
def controlCases : List Control :=
  [{label := "empty", source := [], result := [], reachable := some [[]]},
   {label := "insufficient-change", source := [quarter, quarter, quarter], result := [quarter, quarter, quarter],
    reachable := some [[quarter, quarter, quarter]]},
   {label := "one-dollar", source := [dollar], result := [coffee],
    reachable := some [[dollar], [coffee], [apple, quarter]]},
   {label := "residual-duplicates", source := [quarter, dollar, quarter], result := [coffee, quarter, quarter],
    reachable := some [[quarter, dollar, quarter], [coffee, quarter, quarter], [apple, quarter, quarter, quarter]]},
   {label := "four-quarters", source := [quarter, quarter, quarter, quarter], result := [coffee],
    reachable := some [[quarter, quarter, quarter, quarter], [dollar], [coffee], [apple, quarter]], work := 3000},
   {label := "exact-target", source := [apple, coffee], result := [apple, coffee],
    reachable := some [[apple, coffee]]},
   {label := "standard-vending", source := [dollar, dollar, quarter, quarter, quarter],
    result := [coffee, coffee, quarter, quarter, quarter], reachable := none, work := 5000}]

def wire (value : Pattern) : String := CettaWire.Term.render (InferenceCettaWire.encodePattern value)

def referenceName : Maude.Term → String
  | .app label [] => (label.splitOn ".").getLast!
  | _ => "non-token"

def queryResults (querySpec : CompleteEmission.Spec) (sources : List Pattern) : Except String (List Pattern) := do
  let querySearch := Complete.Normalized.search querySpec.plan [] querySpec.expected .canonical
  let mut results := []
  for source in sources do
    let requested := Pattern.apply ACUBagQuery.requestName [source]
    let start := Mettapedia.Machines.ResumableSearchRunner.Machine.begin querySearch
      (Complete.Normalized.commit querySpec.plan .canonical requested)
    let machine := Mettapedia.Machines.ResumableSearchRunner.Machine.advance querySearch 2 3000 start
    unless machine.phase == .done do throw "source-pattern matching remains pending"
    match machine.state with
    | .apply label [.collection .hashBag parts none] =>
      unless label == ACUBagQuery.resultName do throw "query returned an unknown result constructor"
      results := .apply wrapper [.collection .hashBag parts none] :: results
    | .apply label [.apply _ _] =>
      unless label == ACUBagQuery.requestName do throw "query returned an unknown request constructor"
    | _ => throw "query returned a malformed result"
  pure results

def controls (language : LanguageDef) (querySpec : CompleteEmission.Spec)
    (solutions : List Pattern) (splitTicks : Nat) (midController finalController : CettaWire.Term)
    (control : Control) : String :=
  let plan := (CompletePlanWire.planTerm (spec language).plan [] [] (.base "Marking")).render
  let standard := (StandardWire.commitTerm (spec language).plan .canonical (CompleteEmission.table (spec language))).render
  let queryPlan := (CompletePlanWire.planTerm querySpec.plan [] [] querySpec.expected).render
  let queryStandard := (StandardWire.commitTerm querySpec.plan .canonical (CompleteEmission.table querySpec)).render
  let expectedSolutions := encodeList InferenceCettaWire.encodePattern solutions
  let expectedStates := encodeList InferenceCettaWire.encodePattern
    ((explored language (bag control.source) control.work).nodes.map (·.state))
  "!(let* (($plan (quote " ++ plan ++ ")) ($standard (quote " ++ standard ++ "))" ++
  " ($source (quote " ++ wire (bag control.source) ++ ")) ($expected (quote " ++ wire (committed language (bag control.result)) ++ "))" ++
  " ($expected-states (quote " ++ expectedStates.render ++ "))" ++
  " ($query-plan (quote " ++ queryPlan ++ ")) ($query-standard (quote " ++ queryStandard ++ "))" ++
  " ($expected-solutions (quote " ++ expectedSolutions.render ++ "))" ++
  " ($expected-query-controller (quote " ++ finalController.render ++ "))" ++
  " ($expected-mid-controller (quote " ++ midController.render ++ "))" ++
  " ($begun (maude-acu:begin $source))" ++
  " ($direct (gslt:runner:advance ClassSearch $plan $standard 10 3000 $begun))" ++
  " ($first (gslt:runner:advance ClassSearch $plan $standard 1 3000 $begun))" ++
  " ($resumed (gslt:runner:advance ClassSearch $plan $standard 9 3000 $first))" ++
  " ($states (maude-acu:explore $source " ++ toString control.work ++ "))" ++
  " ($solutions (gslt:maude-query:filter $query-plan $query-standard " ++
    (CettaWire.Term.string ACUBagQuery.requestName).render ++ " " ++
    (CettaWire.Term.string ACUBagQuery.resultName).render ++ " " ++
    (CettaWire.Term.string wrapper).render ++ " $states LNil 64 3000))" ++
  " ($pending-query (gslt:maude-query:filter $query-plan $query-standard " ++
    (CettaWire.Term.string ACUBagQuery.requestName).render ++ " " ++
    (CettaWire.Term.string ACUBagQuery.resultName).render ++ " " ++
    (CettaWire.Term.string wrapper).render ++ " $states LNil 0 3000))" ++
  " ($is-pending (case $pending-query (((MaudeQueryPending $p $s $r $a $w $controller) true) ($other false))))" ++
  " ($resumed-query (gslt:maude-query:resume $pending-query 64 3000))" ++
  " ($query-begun (gslt:maude-query:begin $query-plan $query-standard " ++
    (CettaWire.Term.string ACUBagQuery.requestName).render ++ " $states LNil))" ++
  " ($query-direct (gslt:maude-query:advance $query-plan $query-standard " ++
    (CettaWire.Term.string ACUBagQuery.requestName).render ++ " " ++
    (CettaWire.Term.string ACUBagQuery.resultName).render ++ " " ++
    (CettaWire.Term.string wrapper).render ++ " 64 3000 $query-begun))" ++
  " ($query-mid (gslt:maude-query:advance $query-plan $query-standard " ++
    (CettaWire.Term.string ACUBagQuery.requestName).render ++ " " ++
    (CettaWire.Term.string ACUBagQuery.resultName).render ++ " " ++
    (CettaWire.Term.string wrapper).render ++ " " ++ toString splitTicks ++ " 3000 $query-begun))" ++
  " ($query-split (gslt:maude-query:advance $query-plan $query-standard " ++
    (CettaWire.Term.string ACUBagQuery.requestName).render ++ " " ++
    (CettaWire.Term.string ACUBagQuery.resultName).render ++ " " ++
    (CettaWire.Term.string wrapper).render ++ " " ++ toString (64 - splitTicks) ++ " 3000 $query-mid)))" ++
  " (case $direct (((ClassMachine $phase $state $pending $states-seen $receipts)" ++
  " (let $checked (println! (MaudeACUNativeControl " ++ reprStr control.label ++
  " (== $phase ClassDone) (== $state $expected) (== $direct $resumed) (== $states $expected-states)" ++
  " (== $solutions $expected-solutions) $is-pending (== $resumed-query $solutions)" ++
  " (== $query-direct $expected-query-controller) (== $query-mid $expected-mid-controller) (== $query-split $query-direct)))" ++
  (if control.label == "standard-vending" then
    " (println! (MaudeQueryPrefixControl (case $query-mid (((MaudeQueryActive $remaining (LCons $answer $answers) $machine) true) ($other false)))))"
   else " true") ++ ")))))\n"

def sourceTheory (sourcePath packetPath : String) : IO (Maude.Theory × Maude.Term) := do
  let input ← IO.FS.readFile sourcePath
  let .ok packets := Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "malformed retained parser packets")
  let trees ← packets.mapM fun
    | .expression [.symbol "result", tree, .symbol "nil"] => pure tree
    | _ => throw (IO.userError "expected complete retained parser results")
  let names : MaudeSourceLowering.Names := {
    operators := Maude.Examples.vending.signature.operators.map MaudeSourceLowering.OperatorBinding.ofOperator
    rules := Maude.Examples.vending.rules.map (·.name) }
  let settings : MaudeSourceLowering.Settings := {names := [("GOLD-VENDING", names)]}
  let meanings := trees.filterMap fun tree => (MaudeSourceLowering.lower input tree settings).toOption
  let first :: rest := meanings | throw (IO.userError "source elaboration refused")
  unless rest.all (fun other => decide (other = first)) do
    throw (IO.userError "retained source alternatives disagree")
  let [selected] := first.modules | throw (IO.userError "expected one source module")
  let .ok theory := selected.closedTheory | throw (IO.userError "imported theory is uncertified")
  let [query] := first.commands | throw (IO.userError "expected one source command")
  unless query.kind == .searchStar && query.conditions.isEmpty &&
      operation.flatten query.source == [dollar, dollar, quarter, quarter, quarter] do
    throw (IO.userError "the standard source search command has changed")
  let some target := query.target | throw (IO.userError "the source search pattern is missing")
  unless operation.flatten target == [apple, coffee, .var "M"] do
    throw (IO.userError "the source search target has changed")
  pure (theory, target)

def main (arguments : List String) : IO Unit := do
  let [directory, sourcePath, packetPath] := arguments
    | throw (IO.userError "expected output, ordinary source and retained parser packets")
  let output := System.FilePath.mk directory
  if ← output.pathExists then throw (IO.userError "output already exists")
  let stdout ← IO.getStdout
  stdout.putStrLn "preparing flat ACU source rows"
  stdout.flush
  let (actual, target) ← sourceTheory sourcePath packetPath
  let some witness := Maude.SchemaLink.check actual Maude.Examples.vending
    | throw (IO.userError "source rows differ from the checked vending schema")
  have signatureSame : actual.signature = Maude.Examples.vending.signature := by
    simpa only [Maude.Theory.named] using congrArg Maude.Theory.signature witness.same
  let selectedOperation : Maude.ACUOperation actual [] := {
    declaration := operation.declaration
    declared := by rw [signatureSame]; exact operation.declared
    arguments := operation.arguments
    associative := operation.associative
    commutative := operation.commutative
    unit := operation.unit
    identity := operation.identity
    unit_sorted := by rw [signatureSame]; exact operation.unit_sorted }
  let .ok language := ACUBagCompilation.prepare selectedOperation
    | throw (IO.userError "source ACU row preparation refused")
  let .ok query := ACUBagQuery.prepare selectedOperation language target
    | throw (IO.userError "source ACU query preparation refused")
  let querySpec : CompleteEmission.Spec :=
    ⟨ACUBagCompilation.plan query.language, [], .base ACUBagQuery.stateSort, .canonical⟩
  unless language.validate.isEmpty && language.rewrites.length == 3 &&
      language.terms.head?.map (·.collectionRepresentation) == some .wrapped do
    throw (IO.userError "compiled ACU declarations failed validation")
  stdout.putStrLn "checking shared plan admission"
  stdout.flush
  unless (CompleteEmission.pendingFor (spec language) .classes).isEmpty do
    throw (IO.userError "shared ACU plan has pending obligations")
  unless (CompleteEmission.pendingFor querySpec .classes).isEmpty do
    throw (IO.userError "shared ACU query plan has pending obligations")
  stdout.putStrLn "shared plan admitted; checking model controls"
  stdout.flush
  let mut referenceCases : List Lean.Json := []
  let mut runtimeControls : List String := []
  for control in controlCases do
    stdout.putStrLn ("starting model " ++ control.label)
    stdout.flush
    let machine := advanced language (bag control.source)
    unless machine.phase == .done && machine.state == committed language (bag control.result) do
      throw (IO.userError s!"{control.label}: runner failed its declared result")
    let first := Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search language)
      1 3000 (begun language (bag control.source))
    let resumed := Mettapedia.Machines.ResumableSearchRunner.Machine.advance (search language) 9 3000 first
    unless CompleteExecution.classMachineTerm (spec language).plan resumed ==
        CompleteExecution.classMachineTerm (spec language).plan machine do
      throw (IO.userError s!"{control.label}: equal-budget model resumption changed the machine")
    let explorer := explored language (bag control.source) control.work
    unless Complete.Settled.settled (search language) explorer do
      throw (IO.userError s!"{control.label}: explorer remains pending at {control.work} rounds")
    let actual := explorer.nodes.map (·.state)
    let .ok solutions := queryResults querySpec actual
      | throw (IO.userError "the source search target did not finish matching")
    let queryBegun := ACUBagQuery.Controller.begin querySpec actual
    let queryDone := ACUBagQuery.Controller.advance querySpec wrapper 64 3000 queryBegun
    let .done collected := queryDone | throw (IO.userError "the total-budget query controller remains pending")
    unless collected == solutions do throw (IO.userError "total-budget query answers differ from independent per-candidate results")
    let nonemptyPrefix := (List.range 64).find? fun ticks =>
      match ACUBagQuery.Controller.advance querySpec wrapper ticks 3000 queryBegun with
      | .active (_ :: _) (_ :: _) _ => true
      | _ => false
    if control.label == "standard-vending" && nonemptyPrefix.isNone then
      throw (IO.userError "no suspension with a retained answer prefix was exercised")
    let splitTicks := nonemptyPrefix.getD 1
    let queryMid := ACUBagQuery.Controller.advance querySpec wrapper splitTicks 3000 queryBegun
    let querySplit := ACUBagQuery.Controller.advance querySpec wrapper (64 - splitTicks) 3000 queryMid
    unless ACUBagQuery.Controller.stateTerm querySpec querySplit == ACUBagQuery.Controller.stateTerm querySpec queryDone do
      throw (IO.userError "model total query budget did not compose")
    if let some reachable := control.reachable then
      let expected := reachable.map (fun parts => committed language (bag parts))
      unless actual.all expected.contains && expected.all actual.contains do
        throw (IO.userError s!"{control.label}: explorer differs from the declared ACU outcomes")
    let outcomes ← actual.mapM fun state => do
      let .apply label [.collection .hashBag parts none] := state
        | throw (IO.userError "an explored state has lost its bag carrier")
      unless label == wrapper do throw (IO.userError "an explored state has a foreign wrapper")
      parts.mapM fun part => do
        let some term := MaudeCompilation.decode? part | throw (IO.userError "an explored component has no source readback")
        pure (referenceName term)
    let substitutions ← solutions.mapM fun state => do
      let .apply _ [.collection .hashBag parts none] := state
        | throw (IO.userError "a query substitution has lost its bag carrier")
      parts.mapM fun part => do
        let some term := MaudeCompilation.decode? part | throw (IO.userError "a query substitution has no source readback")
        pure (referenceName term)
    runtimeControls := runtimeControls ++ [controls language querySpec solutions splitTicks
      (ACUBagQuery.Controller.stateTerm querySpec queryMid) (ACUBagQuery.Controller.stateTerm querySpec queryDone) control]
    referenceCases := referenceCases ++ [Lean.Json.mkObj [("label", .str control.label),
      ("source", Lean.toJson (control.source.map referenceName)), ("reachable", Lean.toJson outcomes),
      ("solutions", Lean.toJson substitutions),
      ("querySplitTicks", Lean.toJson splitTicks), ("queryPrefixRetained", .bool nonemptyPrefix.isSome),
      ("settled", .bool true), ("work", Lean.toJson control.work)]]
    stdout.putStrLn s!"model {control.label}: nodes={actual.length}, complete runner"
    stdout.flush
  let .ok emitted := CompleteEmission.emitText? (spec language) "maude-acu" .classes
    | throw (IO.userError "shared emission refused the flat ACU profile")
  let .ok emittedQuery := CompleteEmission.emitText? querySpec "maude-acu-query" .classes
    | throw (IO.userError "shared emission refused the ACU query profile")
  let controlText := String.join runtimeControls
  let parsedControls ← match Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics.readProgram controlText with
    | .ok parsed => pure parsed
    | .error error => do
      IO.FS.createDirAll output
      IO.FS.writeFile (output / "malformed-controls.metta") controlText
      throw (IO.userError s!"generated native controls are malformed: {reprStr error}")
  unless parsedControls.initializers.length == controlCases.length do
    throw (IO.userError "generated native controls were not all retained")
  IO.FS.createDirAll output
  IO.FS.writeFile (output / "machine.metta") (emitted ++ "\n" ++ emittedQuery)
  IO.FS.writeFile (output / "controls.metta") controlText
  IO.FS.writeFile (output / "reference-cases.json") (Lean.toJson referenceCases).pretty
  IO.FS.writeFile (output / "scope.json") (Lean.Json.mkObj [
    ("scope", .str "ground flat ACU transition component; actual GOLD-VENDING rules"),
    ("controls", Lean.toJson controlCases.length), ("checksPerEngine", Lean.toJson (10 * controlCases.length + 1)),
    ("sourceElaborationConnected", .bool true), ("completeSchemaLinkChecked", .bool true),
    ("sourceTargetExecuted", .bool true),
    ("universalACUCompleteness", .bool false), ("fullM0Qualified", .bool false)]).pretty

end MaudeACUControls

def main := MaudeACUControls.main
