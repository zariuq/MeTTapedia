import Mettapedia.Languages.HOLLight.NumberedReplay
import Mettapedia.Languages.HOLLight.RecordedSourceImport
import Mettapedia.Languages.HOLLight.ExportReceiptHistory
import Mettapedia.Languages.HOLLight.SourceProfileModels

/-! Numbered source syntax through the existing registered checker, under the
fixed standard policy. The adapter retains the actual replay equation after
every accepted event. Syntax parsing grants no theorem authority. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGReceive

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open DefinitionAdapters SignatureFormation ProofExecution ExportReplay

structure Input where
  types : Array Json
  terms : Array Json
  events : Array Json

structure Reading where
  input : Input
  types : Array (Option Ty)
  terms : Array (Option SourceTerm)
  registered : ExportReplay.State
  symbols : ExportCodec.Symbols
  sourceConclusions : Std.TreeMap Nat SourceTerm := {}
  history : ExportReceiptHistory.History SourceProfile.primitiveContext SourceProfileModels.policy registered
  refusalChecks : Nat := 0

abbrev Read := StateT Reading (Except String)

def fail {A : Type} (message : String) : Read A := throw message

def jsonNat (value : Json) : Read Nat :=
  NumberedReplay.jsonNat value

def jsonText (value : Json) : Read String :=
  NumberedReplay.jsonText value

def jsonArray (value : Json) : Read (Array Json) :=
  NumberedReplay.jsonArray value

def field (value : Json) (key : String) : Read Json :=
  NumberedReplay.field value key

def arrayAt (values : Array Json) (index : Nat) : Read Json :=
  NumberedReplay.arrayAt values index

def option {A : Type} (value : Option A) (message : String) : Read A :=
  match value with
  | some value => pure value
  | none => fail message

def syntaxReader : NumberedReplay.Syntax Reading where
  types :=
    ⟨(·.input.types), Reading.types, fun state index entry =>
      { state with types := state.types.set! index (some entry) }⟩
  terms :=
    ⟨(·.input.terms), Reading.terms, fun state index entry =>
      { state with terms := state.terms.set! index (some entry) }⟩
  symbols := Reading.symbols
  checkRowArity := true

opaque sourceType (index : Nat) : Read Ty :=
  syntaxReader.readType index

opaque sourceTerm (index : Nat) : Read SourceTerm :=
  syntaxReader.readTerm index

def canonical (index : Nat) : Read CanonicalTerm := do
  option (← sourceTerm index).check s!"ill-typed term {index}"

def checked (index : Nat) : Read CheckedSourceTerm := do
  option (ExportReplay.checkedSource? (← sourceTerm index)) s!"ill-typed source {index}"

def termReader : NumberedReplay.TermReader Reading :=
  ⟨sourceType, sourceTerm, canonical, checked⟩

def registry : NumberedReplay.Registry Reading where
  registered := Reading.registered
  symbols := Reading.symbols
  withSymbols state symbols := { state with symbols }
  sourceConclusions := Reading.sourceConclusions
  policy _ := SourceProfileModels.policy
  decidePolicy _ := inferInstance
  install before event after accepted sources refusals :=
    { before with
      registered := after
      history := ExportReceiptHistory.apply_history SourceProfile.primitiveContext
        SourceProfileModels.policy before.history accepted
      sourceConclusions := ExportCodec.addConclusions before.sourceConclusions event.sourceIds sources
      refusalChecks := before.refusalChecks + refusals }
  registered_install _ _ _ _ _ _ := rfl

def claim (value : Json) : Read (Nat × Sequent × SourceTerm) :=
  NumberedReplay.claim termReader value

def parent (source : Nat) : Read (Nat × Theorem) :=
  NumberedReplay.parent registry source

def acceptEvent (event : Event) (claims : List SourceTerm) : Read Unit :=
  NumberedReplay.acceptEvent registry event claims "registered source event refused"

def receiveEvent (source : Json) : Read Unit :=
  NumberedReplay.receiveEvent termReader registry true .registered
    (NumberedReplay.finish termReader registry .registered) source

def start (input : Input) : Reading where
  input := input
  types := Array.replicate input.types.size none
  terms := Array.replicate input.terms.size none
  registered := SourceProfile.primitiveBasis.received
  symbols := SourceProfile.primitiveBasis.symbols
  history := ExportReceiptHistory.empty_history SourceProfile.primitiveContext SourceProfileModels.policy

theorem registered_history (reading : Reading) :
    Registered.replayFrom SourceProfileModels.policy (Registered.empty SourceProfile.primitiveContext)
      (reading.registered.receipts.toList.map ExportReplay.Event.command) = some reading.registered.registered :=
  ExportReceiptHistory.registered_history SourceProfile.primitiveContext SourceProfileModels.policy
    reading.registered reading.history

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGReceive
