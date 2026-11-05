import Mettapedia.GSLT.LanguageDef.CettaWireData
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution

/-! One emission path for prepared Datalog IR. Executable MeTTa and physical
data payloads have distinct renderers; both native preparation and command-line
source compilation use this operation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Emission

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

structure Result where
  definitions : String
  dictionary : String
  programPayload : String

def entryValid (entry : String) : Bool :=
  let letter := fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
  match entry.toList with
  | [] => false
  | first :: rest => letter first && rest.all (fun c =>
      letter c || ('0' ≤ c && c ≤ '9') || c == ':' || c == '-')

def emit (prepared : Executable.Prepared) (entry : String) : Except String Result := do
  unless entryValid entry do .error "invalid execution entry prefix"
  let spec := ClosureMachine.spec prepared prepared.seedFacts
  let _ ← (CompleteEmission.emitText? spec entry .classes).mapError
    (fun _ => "GSLT execution admission refused")
  let plan := (CompletePlanWire.planTerm spec.plan spec.plan.snapshot.freeTypes [] (.base "DlStatement")).render
  let standard := (ClosureMachine.standardTerm prepared).render
  let source := CettaWire.Term.render (InferenceCettaWire.encodePattern (Executable.request prepared.vocabulary))
  let metadata := (ClosureMachine.metadataTerm prepared).render
  let static := (encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows).render
  let facts := (encodeList InferenceCettaWire.encodePattern prepared.seedFacts).render
  let declarations := "(: " ++ entry ++ ":begin (-> %Undefined%))\n" ++
    "(= (" ++ entry ++ ":begin) (let* (($plan (quote " ++ plan ++ ")) ($standard (quote " ++ standard ++
    ")) ($source (quote " ++ source ++ ")) ($metadata (quote " ++ metadata ++ ")) ($static (quote " ++ static ++
    ")) ($facts (quote " ++ facts ++ "))) (gslt:snapshot:begin $plan $standard $source $metadata " ++ reprStr Query.factRelation ++ " $static $facts)))\n" ++
    "(: " ++ entry ++ ":run (-> Atom Atom %Undefined%))\n" ++
    "(= (" ++ entry ++ ":run $ticks $quantum) (let $initial (" ++ entry ++ ":begin) (gslt:snapshot:advance $initial $ticks $quantum)))\n" ++
    "(: " ++ entry ++ ":resume (-> Atom Atom Atom %Undefined%))\n" ++
    "(= (" ++ entry ++ ":resume $machine $ticks $quantum) (gslt:snapshot:advance $machine $ticks $quantum))\n"
  let sources := RuleExecutionProgram.scopedSource :: CollectionOccurrenceSearchExecution.SelectedNativeSource.sources
  let definitions := String.intercalate "\n" (sources.map (·.text)) ++ "\n" ++
    SnapshotClosureExecution.source.text ++ "\n" ++ declarations
  let dictionary := CettaWire.encodeList (fun (name,value) => Term.application "Binding"
    [.string name,InferenceCettaWire.encodePattern value]) (Executable.dictionary prepared.vocabulary)
  pure ⟨definitions,CettaWireData.render dictionary,
    CettaWireData.render (InferenceCettaWire.encodePattern (IRCodec.program prepared.source))⟩

example : entryValid "lang:compiled" = true := by decide +kernel
example : entryValid "bad) !(inject)" = false := by decide +kernel
example : entryValid "0bad" = false := by decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Emission
