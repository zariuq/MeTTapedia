import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtomRead
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIREmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxNativePlan
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendSource
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinter
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.SnapshotClosureExecution
import Mettapedia.Machines.SelectiveRowCapture
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCatalogueVerification
import Mettapedia.Data.HexBytes

/-! Pure preparation for an in-process source compiler provider. Source
reading, captured input interpretation and emitted execution remain separate
stages. These functions prepare code and decode data; they do not derive the
Datalog closure on the host. File access and native parser execution belong
to the caller. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

open Lean
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.Datalog
open Mettapedia.Languages.MeTTa.PeTTa
private abbrev HostAtom := Mettapedia.Languages.MeTTa.OSLFCore.Atom
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open DatalogIR

/-- Force the actual scalar codec's lazy permanent bounds during foreign
runtime initialization, before request allocations begin. The scalar seed
keeps the calls to the codec visible to native compilation. -/
@[export cetta_datalog_force_integer_bounds_v1]
def forceIntegerBounds (seed : UInt64) : Bool :=
  Mettapedia.Languages.Datalog.Value.fits64 (.number (Int.ofNat seed.toNat)) &&
    Mettapedia.Languages.Datalog.Value.fits64 (.unsigned seed.toNat)

/-- Decimal transport shares the standard library's lazy power table. -/
@[export cetta_datalog_force_decimal_codec_v1]
def forceDecimalCodec (word : UInt64) : String := toString word.toNat

def readProgram (source packet : String) : Except String Program := do
  let .ok [tree] := SpaceSemantics.readSource packet
    | .error "expected one whole-input syntax packet"
  SouffleDatalog.Frontend.read source tree

def hostValue (type : AttributeType) : HostAtom → Option Mettapedia.Languages.Datalog.Value
  | .grounded (.string text) => if type == .symbol then some (.symbol text) else none
  | .grounded (.int value) => match type with
    | .number => if Mettapedia.Languages.Datalog.Value.fits64 (.number value) then some (.number value) else none
    | .unsigned => if 0 ≤ value && Mettapedia.Languages.Datalog.Value.fits64 (.unsigned value.toNat) then some (.unsigned value.toNat) else none
    | _ => none
  | _ => none

def inputRelations (program : Program) : List QualifiedName :=
  program.statements.filterMap fun statement => match statement with
    | .input name => some name
    | _ => none

/-- Distinct declared relations must keep distinct host spellings. -/
def hostNamesValid (separator : String) (program : Program) : Bool :=
  let names := (ProgramStatic.declarations program).map (·.name)
  names.all fun first => names.all fun second =>
    decide (first = second) ||
      decide (String.intercalate separator first ≠ String.intercalate separator second)

/-- Namespace spelling is a host adapter parameter, not Datalog semantics.
Each input occurrence is read independently, before set closure is selected. -/
def captureRow (separator : String) (program : Program) (row : HostAtom) : Except String (List GroundFact) := do
    match row with
    | .expression (.symbol head :: values) =>
      match (inputRelations program).find? (fun name => String.intercalate separator name == head) with
      | none => pure []
      | some name =>
        let some types := ProgramStatic.signature program name | .error "undeclared input relation"
        unless types.length == values.length do .error s!"wrong input arity: {head}"
        let some decoded := (types.zip values).mapM (fun (type,value) => hostValue type value)
          | .error s!"non-ground or ill-typed input fact: {head}"
        pure [⟨name,decoded⟩]
    | .symbol head =>
      if (inputRelations program).any (fun name => String.intercalate separator name == head) then
        .error s!"input fact must be an application: {head}"
      else pure []
    | _ => pure []

def capture (separator : String) (program : Program) (rows : List HostAtom) : Except String (List GroundFact) := do
  Mettapedia.Machines.SelectiveRowCapture.collect (captureRow separator program) rows

def program? (wire : String) : Except String Program := do
  let .ok [host] := SpaceSemantics.readSource wire | .error "expected one program payload"
  let some term := CettaWireAtom.decode? host | .error "invalid program carrier"
  let some pattern := InferenceCettaWire.decodePattern term | .error "invalid program pattern"
  let some program := IRCodec.program? pattern | .error "invalid Datalog IR"
  pure program

def read (source packet separator : String) : Except String Json := do
  let program ← readProgram source packet
  unless hostNamesValid separator program do .error "host relation spelling collision"
  let canonical ← SouffleDatalog.SourcePrinter.print? program
  let inputs := (inputRelations program).map (String.intercalate separator)
  pure (Json.mkObj [
    ("program", .str (CettaWireData.render (InferenceCettaWire.encodePattern (IRCodec.program program)))),
    ("canonical", .str canonical), ("inputs", toJson inputs)])

def prepare (wire facts separator entry : String) : Except String Json := do
  let program ← program? wire
  unless hostNamesValid separator program do .error "host relation spelling collision"
  let rows ← SpaceSemantics.readSource facts
  let seeds ← capture separator program rows
  let prepared ← Executable.prepare program seeds
  let emitted ← DatalogIR.Emission.emit prepared entry
  pure (Json.mkObj [("definitions",.str emitted.definitions), ("dictionary",.str emitted.dictionary),
    ("entry",.str entry), ("seedCount",toJson prepared.seedFacts.length)])

private def binding? : CettaWire.Term → Option (String × Pattern)
  | .application "Binding" [.string name, value] => do
    pure (name, ← InferenceCettaWire.decodePattern value)
  | _ => none

private def physical (text : String) : Except String CettaWire.Term := do
  let .ok [host] := SpaceSemantics.readSource text | .error "expected one data payload"
  let some value := CettaWireAtom.decode? host | .error "invalid data carrier"
  pure value

private def evidenceBytes (text : String) : Except String (List UInt8) := do
  let some bytes := Mettapedia.Data.HexBytes.decode? text
    | .error "expected hexadecimal parser evidence bytes"
  pure bytes

structure SourceEvidence where
  packets : List HostAtom
  forest : List UInt8
  identity : List UInt8
  rounds : Nat

def readSourceEvidence (packet forest identity allowance : String) : Except String SourceEvidence := do
  let .ok [.expression (.symbol "SourceValuesV1" :: packets)] := SpaceSemantics.readSource packet
    | .error "expected a whole-input syntax catalogue"
  let forestBytes ← evidenceBytes forest
  let identityBytes ← evidenceBytes identity
  let some rounds := allowance.toNat? | .error "expected a natural verification allowance"
  pure ⟨packets,forestBytes,identityBytes,rounds⟩

def verificationSpec : Portable.SyntaxDescription :=
  ⟨SouffleDatalog.SourceViews.grammar, SouffleDatalog.SourceViews.profile⟩

def verificationReply : Option Bool → Except String Json
  | none => .ok (Json.mkObj [("status",.str "pending")])
  | some false => .error "source forest or selected catalogue failed independent verification"
  | some true => .ok (Json.mkObj [("status",.str "verified")])

/-- Both coverage and catalogue checking are independent of the recognizer.
An unfinished check asks for another allowance; it never admits a packet. -/
def verifySource (source packet forest identity allowance : String) : Except String Json := do
  let evidence ← readSourceEvidence packet forest identity allowance
  verificationReply (SourceCatalogueVerification.verify? verificationSpec SouffleDatalog.SourcePolicy.filters
    source evidence.forest evidence.identity evidence.packets evidence.rounds)

private def valueJson : Mettapedia.Languages.Datalog.Value → Json
  | .symbol text => Json.mkObj [("kind",.str "string"),("value",.str text)]
  | .number value => Json.mkObj [("kind",.str "number"),("value",.str (toString value))]
  | .unsigned value => Json.mkObj [("kind",.str "unsigned"),("value",.str (toString value))]
  | .floating word => Json.mkObj [("kind",.str "floating"),("value",.str (toString word.toNat))]

/-- Observation decodes data only. It performs no source inference and does
not identify a suspended machine with a completed result. -/
def observe (wire dictionary facts separator : String) : Except String Json := do
  let program ← program? wire
  unless hostNamesValid separator program do .error "host relation spelling collision"
  let some bindings := CettaWire.decodeList binding? (← physical dictionary)
    | .error "invalid result dictionary"
  let some patterns := CettaWire.decodeList InferenceCettaWire.decodePattern (← physical facts)
    | .error "invalid result fact list"
  let outputRelations := program.statements.filterMap fun statement => match statement with
    | .output name => some name | _ => none
  let decoded ← patterns.mapM fun pattern => do
    let some fact := IRCodec.groundFact? (Mettapedia.OSLF.MeTTaIL.Match.applyBindings bindings pattern)
      | .error "invalid ground result fact"
    pure fact
  let outputs := decoded.filter (fun fact => fact.relation ∈ outputRelations)
  pure (Json.mkObj [("facts",toJson (outputs.eraseDups.map fun fact =>
    Json.mkObj [("relation",.str (String.intercalate separator fact.relation)),
      ("values",toJson (fact.values.map valueJson))]))])

def answer (result : Except String Json) : String :=
  (match result with
   | .ok value => Json.mkObj [("ok",.bool true),("value",value)]
   | .error message => Json.mkObj [("ok",.bool false),("message",.str message)]).compress

/-- The compiler's authored source/core binding, independent of resource
locations and editor preferences. -/
structure Components where
  sourceSyntax : Value
  core : Value
  parserPlan : Value
  execution : Value
  deriving DecidableEq

def compilerRecord (uri : String) : Value := .record [
  ("resource",.string uri),("verify",.string "verify"),("read",.string "read"),("prepare",.string "prepare"),
  ("observe",.string "observe"),("namespaceSeparator",.string ":")]

def components : Except String Components := do
  let some description := SouffleDatalog.syntaxDescription? | .error "source grammar/profile admission failed"
  let some plan := SourceSyntaxExport.plan? description | .error "source parser compilation failed"
  let lines := fun terms => String.intercalate "\n" (SourceSyntaxNativePlan.canonicalRows terms) ++ "\n"
  let parserPlan : Value := .record [
    ("productions",.string (lines (SourceSyntaxNativePlan.productions plan))),
    ("classes",.string (lines (plan.lexical.classes.flatMap SourceSyntaxExport.classClauses))),
    ("start",.string (SourceSyntaxExport.state plan.lexical.startSort).render),
    ("selection",.string ((CettaWire.Term.application "source-selection-v1"
      [CettaWire.encodeList SourceSyntaxNativePlan.directFilter SouffleDatalog.SourcePolicy.filters]).render))]
  let runtime : Value := .record [("profile",.string "scoped-snapshot-closure-v1"),
    ("language",.string "petta"),("hostProfile",.string "extended"),
    ("observation",.string "declared-output-fact-set")]
  let some core := SouffleDatalog.programData? | .error "operational core admission failed"
  pure ⟨(Portable.syntaxExport "syntax" description).spec,
    Value.Wire.quoteTerm (Portable.coreCodec.encode core),parserPlan,runtime⟩

def compilerCompatible (compiler : Value) : Bool :=
  match compiler with
  | .record fields => match Value.field? fields "resource" with
    | some (.string uri) => decide (compiler = compilerRecord uri)
    | _ => false
  | _ => false

def bindComponents (expected supplied : Components) (compiler : Value) : Except String Components :=
  if compilerCompatible compiler && decide (supplied = expected) then .ok expected
  else .error "source, core, parser plan or execution does not match this compiler"

def admitComponents (supplied : Components) (compiler : Value) : Except String Components := do
  let expected ← components
  bindComponents expected supplied compiler

private def component (text : String) : Except String Value := do
  let some value := Value.Wire.decode? (← physical text) | .error "invalid component carrier"
  pure value

/-- A fixed receipt is issued only by comparing the supplied components to
this provider's source/core binding. The loader calls this operation itself;
no caller-provided receipt can create a bound language value. -/
@[export cetta_datalog_admit_v1]
def nativeAdmit (source core plan execution compiler : String) : String :=
  let result := do
    let supplied : Components := ⟨← component source,← component core,← component plan,← component execution⟩
    admitComponents supplied (← component compiler)
  match result with
  | .ok _ => "SourceBindingAcceptedV1"
  | .error reason => answer (.error reason)

/-- A closed module/1 package built from the authored source components.
The compiler URI is interpreted relative to the package by its loader. -/
def package (compilerURI : String) : Except String Json := do
  let bound ← components
  let envelope : RawModule := ⟨"Datalog",[],[
    ⟨"syntax",bound.sourceSyntax⟩,⟨"parserPlan",bound.parserPlan⟩,⟨"core",bound.core⟩,
    ⟨"compiler",compilerRecord compilerURI⟩,⟨"execution",bound.execution⟩,
    ⟨"regions",.record [("preferredRawFenceDepth",.integer 1)]⟩]⟩
  let some checked := decode? upstreamLimits (encodeRaw envelope) | .error "invalid package envelope"
  pure (Json.mkObj [("module",.str ("(module:document " ++ CettaWireData.render (Value.Wire.encode (encodeRaw checked.val)) ++ ")"))])

@[export cetta_datalog_package_v1]
def nativePackage (compilerURI : String) : String := answer (package compilerURI)

@[export cetta_datalog_read_v1]
def nativeRead (source packet separator : String) : String := answer (read source packet separator)

@[export cetta_datalog_verify_v1]
def nativeVerify (source packet forest identity allowance : String) : String :=
  answer (verifySource source packet forest identity allowance)

@[export cetta_datalog_prepare_v1]
def nativePrepare (wire facts separator entry : String) : String := answer (prepare wire facts separator entry)

@[export cetta_datalog_observe_v1]
def nativeObserve (wire dictionary facts separator : String) : String := answer (observe wire dictionary facts separator)

theorem readProgram_source (source packet : String) (program : Program)
    (accepted : readProgram source packet = .ok program) :
    ∃ tree, SpaceSemantics.readSource packet = .ok [tree] ∧
      SouffleDatalog.Frontend.read source tree = .ok program := by
  unfold readProgram at accepted
  split at accepted
  next tree equation => exact ⟨tree, equation, accepted⟩
  next => cases accepted

example : hostValue .unsigned (.grounded (.int (-1))) = none := by decide +kernel
example : hostValue .symbol (.symbol "unquoted") = none := rfl
example : capture ":" ⟨[.declaration ⟨["Edge"],[⟨"x",.symbol⟩]⟩,.input ["Edge"]]⟩
    [.expression [.symbol "Edge",.grounded (.string "a")]] =
      .ok [⟨["Edge"],[.symbol "a"]⟩] := by decide +kernel


end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler
