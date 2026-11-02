import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureMachine
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassSearch
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! Native closure frames retain the same compiled plan, contextual binding
readouts and raw class receipts used by the common execution machinery. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine

open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def metadataTerm (prepared : Executable.Prepared) : Term := encodeList (fun (ordinal,clause) =>
  .application "SnapshotClause" [.natural ordinal,
    encodeList (fun name => .application "SnapshotVariable" [.string name,.string (Join.logicalVariable name)])
      (DerivationIdentity.clauseVariables clause),.natural clause.positiveAtoms.length])
    (LPBridge.numberedClauses prepared.source)

def keyTerm (key : Key) : Term := .application "SnapshotKey" [.natural key.statementIndex,
  encodeList (fun (name,value) => .application "Binding" [.string name,InferenceCettaWire.encodePattern value]) key.grounding,
  encodeList InferenceCettaWire.encodePattern key.premises]

def epochTerm (epoch : Epoch) : Term := .application "SnapshotEpoch" [.natural epoch.ordinal,
  encodeList InferenceCettaWire.encodePattern epoch.facts,
  encodeList CompleteExecution.classReceiptTerm epoch.receipts]

def spec (prepared : Executable.Prepared) (facts : List Pattern) : CompleteEmission.Spec :=
  ⟨Executable.plan prepared facts,[],.base "DlStatement",.standard⟩

def standardTerm (prepared : Executable.Prepared) : Term :=
  StandardWire.commitTerm (Executable.plan prepared []) .standard (CompleteEmission.table (spec prepared []))

def machineTerm (prepared : Executable.Prepared) (machine : Machine prepared) : Term :=
  match machine.fault with
  | some fault => .application "SnapshotFailure" [.symbol (match fault with
    | .invalidProvider => "InvalidProvider" | .invalidReceipt => "InvalidReceipt")]
  | none => .application "SnapshotClosure" [
    .symbol (if machine.complete then "SnapshotComplete" else "SnapshotPending"),.natural machine.round,
    CompletePlanWire.planTerm (Executable.plan prepared machine.facts) (Executable.freeTypes prepared.vocabulary) [] (.base "DlStatement"),
    standardTerm prepared,InferenceCettaWire.encodePattern (Executable.request prepared.vocabulary),metadataTerm prepared,
    .string Query.factRelation,encodeList PremiseOperationsExecution.GeneralExecution.providerRowTerm prepared.staticRows,
    encodeList InferenceCettaWire.encodePattern machine.facts,encodeList keyTerm machine.keys,
    encodeList epochTerm machine.history,CompleteExecution.classStateTerm (Executable.plan prepared machine.facts) machine.run]

def resultTerm (prepared : Executable.Prepared) (machine : Machine prepared) : Term :=
  match machine.fault with
  | some _ => machineTerm prepared machine
  | none => .application "SnapshotResult" [.symbol (if machine.complete then "SnapshotComplete" else "SnapshotPending"),
      .natural machine.round,encodeList InferenceCettaWire.encodePattern machine.facts,encodeList keyTerm machine.keys]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.ClosureMachine
