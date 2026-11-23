import Mettapedia.Languages.HOLLight.NumberedReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CheckedSourceNodes
import Mettapedia.Languages.HOLLight.RecordedSourceImport
import Mettapedia.Languages.HOLLight.ExportReceiptHistory
import Mettapedia.Languages.HOLLight.SourceProfileModels

/-! Numbered source syntax through the existing registered checker, under the
fixed standard policy. The adapter retains the actual replay equation after
every accepted event. Syntax parsing grants no theorem authority. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGMemoReceive

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
  checkedNodes : Std.TreeMap Nat CheckedSourceTerm := {}
  canonicalNodes : Std.HashMap (Nat × List Nat) CheckedSourceNodes.Entry := {}
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

def checkedNode (index : Nat) : Read CheckedSourceTerm := do
  let source ← sourceTerm index
  let state ← get
  if let some cached := state.checkedNodes[index]? then
    if let some retained := CheckedSourceNodes.retarget? cached source then return retained
  let row ← jsonArray (← option state.input.terms[index]? "missing typed source node")
  let result ← match source with
    | .const symbol type => pure (CheckedSourceNodes.constant symbol type)
    | .var name type => pure (CheckedSourceNodes.variableNode name type)
    | .app _ _ => do
      let left ← jsonNat (← arrayAt row 1)
      let right ← jsonNat (← arrayAt row 2)
      if _earlier : left < index ∧ right < index then
        let function ← checkedNode left
        let argument ← checkedNode right
        option (CheckedSourceNodes.application? function argument) "typed application refused"
      else fail "non-earlier typed source application"
    | .abs name domain _ => do
      let inside ← jsonNat (← arrayAt row 2)
      if _earlier : inside < index then
        pure (CheckedSourceNodes.abstraction name domain (← checkedNode inside))
      else fail "non-earlier typed source abstraction"
  let result ← option (CheckedSourceNodes.retarget? result source) "typed source node shape differs"
  modify fun state => { state with checkedNodes := state.checkedNodes.insert index result }
  return result
termination_by index
decreasing_by all_goals omega

def translatedNode (index : Nat) (keys : List Nat) (binders : List SourceVar) :
    Read CheckedSourceNodes.Entry := do
  let source ← sourceTerm index
  let state ← get
  if let some cached := state.canonicalNodes[(index,keys)]? then
    if let some retained := cached.use? source binders then return ⟨source, binders, retained⟩
  let row ← jsonArray (← option state.input.terms[index]? "missing canonical source node")
  let result : CheckedSourceNodes.Entry ← match source with
    | .const symbol type => pure ⟨.const symbol type, binders, CheckedSourceNodes.Image.constant symbol type binders⟩
    | .var name type => pure ⟨.var name type, binders, CheckedSourceNodes.Image.variable name type binders⟩
    | .app function argument => do
      let left ← jsonNat (← arrayAt row 1)
      let right ← jsonNat (← arrayAt row 2)
      if _earlier : left < index ∧ right < index then
        let functionEntry ← translatedNode left keys binders
        let argumentEntry ← translatedNode right keys binders
        let functionImage ← option (functionEntry.use? function binders) "function image scope differs"
        let argumentImage ← option (argumentEntry.use? argument binders) "argument image scope differs"
        pure ⟨.app function argument, binders, CheckedSourceNodes.Image.application functionImage argumentImage⟩
      else fail "non-earlier canonical source application"
    | .abs name domain body => do
      let binder ← jsonNat (← arrayAt row 1)
      let inside ← jsonNat (← arrayAt row 2)
      if _earlier : inside < index then
        let following := (⟨name,domain⟩ : SourceVar) :: binders
        let bodyEntry ← translatedNode inside (binder :: keys) following
        let bodyImage ← option (bodyEntry.use? body following) "body image scope differs"
        pure ⟨.abs name domain body, binders, CheckedSourceNodes.Image.abstraction name domain bodyImage⟩
      else fail "non-earlier canonical source abstraction"
  modify fun state => { state with canonicalNodes := state.canonicalNodes.insert (index,keys) result }
  return result
termination_by index
decreasing_by all_goals omega

def canonical (index : Nat) : Read CanonicalTerm := do
  let checked ← checkedNode index
  let translated ← translatedNode index [] []
  let image ← option (translated.use? checked.source []) "closed canonical image differs"
  return CheckedSourceNodes.canonical checked image

def checked (index : Nat) : Read CheckedSourceTerm := checkedNode index

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

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.SourceDAGMemoReceive
