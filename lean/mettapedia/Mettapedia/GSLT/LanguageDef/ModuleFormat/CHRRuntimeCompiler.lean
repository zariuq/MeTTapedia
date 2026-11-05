import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompilerProtocol
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxNativePlan
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRExecutionData
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologFrontend
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologPrinter
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgramCodec
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRScalarReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CHRLangAdapterSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RuleExecutionProgram
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.PremiseOperationsExecution.RestSchemaPrimitives
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorTyping
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.ConstructorScan
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.RetainedOperations
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationAdvance
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionPresentationExecution.AllocationChildren

/-! Pure preparation for the ground CHR language package. Source reading,
captured-occurrence interpretation, preparation and final-store observation
are separate stages. These functions prepare MeTTa code and decode data;
the refined CHR execution itself runs in MeTTa through the package port.

Posting order is the captured occurrences in their capture order, then the
source query in source order. The observation names the captured
occurrences that the run consumed and the final occurrences it created. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler

open Lean
open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open SourceCompilerProtocol

/-- Lean creates some closed constants on first use. Forcing them during
provider initialization keeps them out of per-request allocation. -/
@[export cetta_chr_force_constants_v1]
def forceConstants (word : UInt64) : String :=
  toString (Int.ofNat word.toNat - Int.ofNat (2 ^ 70)) ++ toString ("-18446744073709551616".toInt?)

/-! ## Source reading -/

/-- The retained ambiguity policy: every selected whole-input interpretation
is read, and all of them must lower to the same independent IR. -/
def readProgram (source catalogue : String) : Except String CHRPrologLowering.Program := do
  let .ok [.expression (.symbol "SourceValuesV1" :: packets)] := SpaceSemantics.readSource catalogue
    | .error "expected the selected whole-input source catalogue"
  let readings ← packets.mapM fun packet => do
    let .expression [.symbol "result", tree, .symbol "nil"] := packet
      | .error "expected an explicitly selected whole-input parser result"
    (·.lowered) <$> CHRPrologFrontend.read source tree
  match readings with
  | [] => .error "no selected source interpretation"
  | first :: rest =>
    if rest.all (fun reading => decide (reading = first)) then pure first
    else .error "CHR source alternatives have different IR interpretations"

def groundArgument? : CHR.Term → Option CHR.Value
  | .value datum => some datum
  | _ => none

def groundConstraint? (head : CHR.Head) : Option CHR.Constraint := do
  pure ⟨head.name, ← head.arguments.mapM groundArgument?⟩

def programValue (lowered : CHRPrologLowering.Program) : Value :=
  CHRProgramCodec.node "ChrLangProgram" [CHRProgramCodec.program lowered.program,
    .list (lowered.inputs.map fun constraint => CHRProgramCodec.head constraint.asHead)]

def programOfValue? (value : Value) : Option CHRPrologLowering.Program := do
  let ("ChrLangProgram", [program, .list inputs]) ← CHRProgramCodec.node? value | none
  let program ← CHRProgramCodec.program? program
  let heads ← inputs.mapM CHRProgramCodec.head?
  pure ⟨program, ← heads.mapM groundConstraint?⟩

def program? (wire : String) : Except String CHRPrologLowering.Program := do
  let some program := programOfValue? (← SourceCompilerProtocol.value? wire)
    | .error "invalid CHR program payload"
  pure program

/-- The constraint names a capture selects. Arity is checked per occurrence. -/
def inputNames (program : CHR.Program) : List String :=
  (program.declarations.map (·.name)).eraseDups

def read (source catalogue _separator : String) : Except String Json := do
  let lowered ← readProgram source catalogue
  pure (Json.mkObj [
    ("program", .str (renderValue (programValue lowered))),
    ("canonical", .str (CHRPrologPrinter.program lowered.program lowered.inputs)),
    ("inputs", toJson (inputNames lowered.program))])

/-! ## Captured occurrences

The engine lends each selected occurrence as a structural record that keeps
its host kind. Only integers, symbols and expressions denote C0 values. -/

inductive HostShape where
  | symbol (name : String)
  | integer (value : Int)
  | expression (items : List HostShape)
  | other (kind : String)
  deriving Repr

def hostShape? : Nat → Json → Option HostShape
  | 0, _ => none
  | fuel + 1, json =>
    match json.getObjVal? "symbol", json.getObjVal? "integer", json.getObjVal? "expression" with
    | .ok (.str name), _, _ => some (.symbol name)
    | _, .ok (.str digits), _ => HostShape.integer <$> digits.toInt?
    | _, _, .ok (.arr items) => HostShape.expression <$> items.toList.mapM (hostShape? fuel)
    | _, _, _ =>
      if (json.getObjVal? "string").toOption.isSome then some (.other "string")
      else if (json.getObjVal? "bool").toOption.isSome then some (.other "Boolean")
      else if (json.getObjVal? "float").toOption.isSome then some (.other "float")
      else if (json.getObjVal? "variable").toOption.isSome then some (.other "variable")
      else match json.getObjVal? "grounded" with
        | .ok (.str kind) => some (.other kind)
        | _ => none

mutual
  def c0Value? : HostShape → Except String CHR.Value
    | .integer number => pure (.integer number)
    | .symbol name => pure (.atom name)
    | .expression items => CHR.Value.tuple <$> c0Values? items
    | .other kind => .error s!"a C0 constraint argument is an integer, symbol or tuple, not a {kind}"
  def c0Values? : List HostShape → Except String (List CHR.Value)
    | [] => pure []
    | first :: rest => do pure ((← c0Value? first) :: (← c0Values? rest))
end

def declared (program : CHR.Program) (name : String) (arity : Nat) : Bool :=
  program.declarations.any fun declaration => declaration.name == name && declaration.arity == arity

/-- Name and arity identify a constraint. Rows that declare no constraint are
not captured; a declared row with a non-C0 argument refuses the run. -/
def captureRow (program : CHR.Program) : HostShape → Except String (Option CHR.Constraint)
  | .expression (.symbol name :: arguments) =>
    if declared program name arguments.length then do
      pure (some ⟨name, ← c0Values? arguments⟩)
    else pure none
  | .symbol name =>
    if declared program name 0 then .error s!"a 0-ary constraint occurrence is written ({name})"
    else pure none
  | _ => pure none

/-- Captured constraints in capture order, each with its selection ordinal. -/
def capture (program : CHR.Program) (rows : List HostShape) :
    Except String (List (Nat × CHR.Constraint)) := do
  let read ← rows.zipIdx.mapM fun (row, ordinal) => do
    pure ((fun constraint => (ordinal, constraint)) <$> (← captureRow program row))
  pure read.reduceOption

def captured? (text : String) : Except String (List HostShape) := do
  let .arr rows ← Json.parse text | .error "expected an array of captured rows"
  let some shapes := rows.toList.mapM (hostShape? (text.length + 1))
    | .error "invalid captured row record"
  pure shapes

/-! ## Preparation -/

/-- The shared GSLT runtime, the integer and CHR controller libraries and the
package port, in the order of the common runtime gate. -/
def runtimeSources : List ProgramQuotation.QuotedProgram :=
  [RuleExecutionProgram.scopedSource,
   PremiseOperationsExecution.RestSchema.source,
   CollectionPresentationExecution.ConstructorTyping.source,
   CollectionPresentationExecution.RetainedConstructors.source,
   CollectionPresentationExecution.RetainedOperations.source,
   CollectionPresentationExecution.AllocationAdvance.source,
   CollectionPresentationExecution.AllocationChildren.source] ++
  CollectionOccurrenceSearchExecution.SelectedNativeSource.sources ++
  [CHRControllerSource.integerSource, CHRControllerSource.source, CHRLangAdapterSource.source]

/-- Search steps per controller tick, and controller ticks per port unit. -/
def quantum : Nat := 20
def ticksPerUnit : Nat := 100

/-- The common package port: begin, one bounded unit of work, and outcome. -/
def portDefinitions (entry : String) : String :=
  "(: " ++ entry ++ ":begin (-> %Undefined%))\n" ++
  "(= (" ++ entry ++ ":begin) (let $machine (" ++ entry ++ ":chr:begin) (gslt:chr-lang:begin $machine)))\n" ++
  "(: " ++ entry ++ ":advance (-> Atom %Undefined%))\n" ++
  "(= (" ++ entry ++ ":advance $run) (gslt:chr-lang:run-ticks $run " ++ toString ticksPerUnit ++ " " ++
    toString quantum ++ "))\n" ++
  "(: " ++ entry ++ ":outcome (-> Atom %Undefined%))\n" ++
  "(= (" ++ entry ++ ":outcome $run) (gslt:chr-lang:outcome $run))\n"

def dictionaryValue (vocabulary : CHRCompilation.Vocabulary) (captured : List Nat) (queries : Nat) : Value :=
  CHRProgramCodec.node "ChrLangDictionary" [.list (vocabulary.predicates.map Value.string),
    .list (vocabulary.scalars.map CHRProgramCodec.value),
    .list (captured.map fun ordinal => Value.integer ordinal), .integer queries]

structure Dictionary where
  vocabulary : CHRCompilation.Vocabulary
  captured : List Nat
  queries : Nat

def dictionary? (text : String) : Except String Dictionary := do
  let some ("ChrLangDictionary", [.list predicates, .list scalars, .list captured, queries]) :=
      CHRProgramCodec.node? (← SourceCompilerProtocol.value? text)
    | .error "invalid CHR result dictionary"
  let some predicates := predicates.mapM fun value => match value with | .string name => some name | _ => none
    | .error "invalid dictionary predicates"
  let some scalars := scalars.mapM CHRProgramCodec.value? | .error "invalid dictionary scalars"
  let some captured := captured.mapM CHRProgramCodec.natural? | .error "invalid captured ordinals"
  let some queries := CHRProgramCodec.natural? queries | .error "invalid query count"
  pure ⟨⟨predicates, scalars⟩, captured, queries⟩

/-- The current host adapter uses native symbols. PeTTa identifies the
uppercase truth spellings with its lowercase truths; empty and NUL-bearing
names cannot be native symbols. Keep these as execution obligations rather
than silently changing a guest atom's identity. -/
def hostSymbolSupported (name : String) : Bool :=
  !name.isEmpty && !name.contains '\u0000' && name != "True" && name != "False"

mutual
  def hostValueSupported : CHR.Value → Bool
    | .integer _ => true
    | .atom name => hostSymbolSupported name
    | .tuple fields => hostValuesSupported fields
  def hostValuesSupported : List CHR.Value → Bool
    | [] => true
    | first :: rest => hostValueSupported first && hostValuesSupported rest
end

def hostVocabularySupported (vocabulary : CHRCompilation.Vocabulary) : Bool :=
  vocabulary.predicates.all hostSymbolSupported && vocabulary.scalars.all hostValueSupported

def prepare (wire rows _separator entry : String) : Except String Json := do
  unless entryValid entry do .error "invalid execution entry prefix"
  let lowered ← program? wire
  let captured ← capture lowered.program (← captured? rows)
  let seeds := captured.map Prod.snd ++ lowered.inputs
  let prepared ← CHRCompilation.prepare lowered.program seeds
  unless hostVocabularySupported prepared.vocabulary do
    return Json.mkObj [("status", .str "unadmitted"),
      ("reason", .str "requires lossless host atom representation: empty, NUL-bearing, True or False")]
  let controller ← CHRCompilation.ExecutionData.emitText? prepared seeds (entry ++ ":chr")
  let runtime := String.intercalate "\n" (runtimeSources.map (·.text))
  pure (Json.mkObj [
    ("definitions", .str (runtime ++ "\n" ++ controller ++ "\n" ++ portDefinitions entry)),
    ("dictionary", .str (renderValue (dictionaryValue prepared.vocabulary (captured.map Prod.fst)
      lowered.inputs.length))),
    ("entry", .str entry), ("captured", toJson (captured.map Prod.fst)),
    ("seedCount", toJson seeds.length)])

/-! ## Observation -/

mutual
  def guestValue? (vocabulary : CHRCompilation.Vocabulary) : Pattern → Option CHR.Value
    | .fvar name => do
      let index ← (List.range vocabulary.scalars.length).find? fun index =>
        CHRCompilation.scalarRef index == .fvar name
      vocabulary.scalars[index]?
    | .apply "ChrTuple" [.collection .vec fields none] => CHR.Value.tuple <$> guestValues? vocabulary fields
    | pattern => CHR.Value.integer <$> CHRCompilation.ScalarReading.integer? pattern
  def guestValues? (vocabulary : CHRCompilation.Vocabulary) : List Pattern → Option (List CHR.Value)
    | [] => some []
    | first :: rest => do pure ((← guestValue? vocabulary first) :: (← guestValues? vocabulary rest))
end

def guestConstraint? (vocabulary : CHRCompilation.Vocabulary) : Pattern → Option CHR.Constraint
  | .apply "ChrConstraint" [.fvar predicate, .collection .vec arguments none] => do
    let index ← (List.range vocabulary.predicates.length).find? fun index =>
      CHRCompilation.predicateRef index == .fvar predicate
    pure ⟨← vocabulary.predicates[index]?, ← guestValues? vocabulary arguments⟩
  | _ => none

def guestOccurrence? (vocabulary : CHRCompilation.Vocabulary) : Pattern → Option (Nat × CHR.Constraint)
  | .apply "ChrOccurrence" [id, constraint] => do
    pure (← CHRCompilation.ScalarReading.occurrence? id, ← guestConstraint? vocabulary constraint)
  | _ => none

mutual
  def valueJson : CHR.Value → Json
    | .integer number => Json.mkObj [("integer", .str (toString number))]
    | .atom name => Json.mkObj [("symbol", .str name)]
    | .tuple fields => Json.mkObj [("expression", .arr (valuesJson fields).toArray)]
  def valuesJson : List CHR.Value → List Json
    | [] => []
    | first :: rest => valueJson first :: valuesJson rest
end

def constraintJson (constraint : CHR.Constraint) : Json :=
  Json.mkObj [("expression", .arr (Json.mkObj [("symbol", .str constraint.name)] ::
    valuesJson constraint.arguments).toArray)]

/-- Captured occurrence `ordinal` survives exactly when its CHR identifier is
in the final store; final occurrences with no captured identifier are new. -/
def consumed (captured : List (Nat × Nat)) (final : List (Nat × CHR.Constraint)) : List Nat :=
  captured.filterMap fun (ordinal, id) => if (final.map Prod.fst).contains id then none else some ordinal

def additions (captured : List (Nat × Nat)) (final : List (Nat × CHR.Constraint)) :
    List (Nat × CHR.Constraint) :=
  final.filter fun (id, _) => !(captured.map Prod.snd).contains id

def faultText (reason : CettaWire.Term) : String := CettaWireData.render reason

def observe (wire dictionary data _separator : String) : Except String Json := do
  let lowered ← program? wire
  let dictionary ← dictionary? dictionary
  let .application "ChrLangResult" [phase, store, seeds] ← physical data
    | .error "invalid CHR outcome payload"
  match phase with
  | .symbol "ChrFailed" => pure (Json.mkObj [("status", .str "failed")])
  | .application "ChrFault" [reason] =>
    pure (Json.mkObj [("status", .str "fault"), ("reason", .str (faultText reason))])
  | .symbol "ChrComplete" =>
    let some occurrences := CettaWire.decodeList InferenceCettaWire.decodePattern store
      | .error "invalid final store"
    let some decoded := occurrences.mapM (guestOccurrence? dictionary.vocabulary)
      | .error "invalid final occurrence"
    let some seedIds := CettaWire.decodeList (fun term =>
        InferenceCettaWire.decodePattern term >>= CHRCompilation.ScalarReading.occurrence?) seeds
      | .error "invalid seed identifiers"
    unless seedIds.length == dictionary.captured.length + dictionary.queries do
      .error "a completed run must have posted every seed"
    let ordered := decoded.mergeSort fun first second => first.1 ≤ second.1
    let finalIds := ordered.map Prod.fst
    unless finalIds.Nodup do .error "final store identifiers are not distinct"
    unless ordered.all (fun (_, constraint) =>
        declared lowered.program constraint.name constraint.arguments.length) do
      .error "final store holds an undeclared constraint"
    let captured := dictionary.captured.zip (seedIds.take dictionary.captured.length)
    let values := ordered.map fun (_, constraint) => constraintJson constraint
    pure (Json.mkObj [("status", .str "complete"), ("values", .arr values.toArray),
      ("publication", Json.mkObj [("kind", .str "transform"), ("mode", .str "multiset"),
        ("consume", toJson (consumed captured ordered)),
        ("additions", .arr ((additions captured ordered).map fun (_, constraint) =>
          constraintJson constraint).toArray)])])
  | _ => .error "invalid CHR outcome phase"

/-! ## Package components -/

structure Components where
  sourceSyntax : Value
  core : Value
  parserPlan : Value
  execution : Value
  deriving DecidableEq

def compilerRecord (uri : String) : Value := .record [
  ("resource", .string uri), ("verify", .string "verify"), ("read", .string "read"),
  ("prepare", .string "prepare"), ("observe", .string "observe"), ("namespaceSeparator", .string ":")]

def executionRecord : Value := .record [("profile", .string "prepared-port-v1"),
  ("language", .string "petta"), ("hostProfile", .string "extended"),
  ("observation", .string "final-constraint-multiset")]

def components : Except String Components := do
  let description := CHRPrologSyntax.description
  let some plan := SourceSyntaxExport.plan? description | .error "source parser compilation failed"
  let lines := fun terms => String.intercalate "\n" (SourceSyntaxNativePlan.canonicalRows terms) ++ "\n"
  let parserPlan : Value := .record [
    ("productions", .string (lines (SourceSyntaxNativePlan.productions plan))),
    ("classes", .string (lines (plan.lexical.classes.flatMap SourceSyntaxExport.classClauses))),
    ("start", .string (SourceSyntaxExport.state plan.lexical.startSort).render),
    ("selection", .string ((CettaWire.Term.application "source-selection-v1"
      [CettaWire.encodeList SourceSyntaxNativePlan.directFilter CHRPrologSyntax.selection]).render))]
  pure ⟨(Portable.syntaxExport "syntax" description).spec,
    Value.Wire.quoteTerm (Portable.coreCodec.encode CHRProgram.language), parserPlan, executionRecord⟩

def compilerCompatible (compiler : Value) : Bool :=
  match compiler with
  | .record fields => match Value.field? fields "resource" with
    | some (.string uri) => decide (compiler = compilerRecord uri)
    | _ => false
  | _ => false

def admitComponents (supplied : Components) (compiler : Value) : Except String Components := do
  let expected ← components
  if compilerCompatible compiler && decide (supplied = expected) then .ok expected
  else .error "source, core, parser plan or execution does not match this compiler"

@[export cetta_chr_admit_v1]
def nativeAdmit (source core plan execution compiler : String) : String :=
  let result := do
    let supplied : Components := ⟨← SourceCompilerProtocol.value? source, ← SourceCompilerProtocol.value? core,
      ← SourceCompilerProtocol.value? plan, ← SourceCompilerProtocol.value? execution⟩
    admitComponents supplied (← SourceCompilerProtocol.value? compiler)
  match result with
  | .ok _ => "SourceBindingAcceptedV1"
  | .error reason => answer (.error reason)

/-- A closed module/1 package; the compiler URI is relative to the package. -/
def package (compilerURI : String) : Except String Json := do
  let bound ← components
  let envelope : RawModule := ⟨"CHR", [], [
    ⟨"syntax", bound.sourceSyntax⟩, ⟨"parserPlan", bound.parserPlan⟩, ⟨"core", bound.core⟩,
    ⟨"compiler", compilerRecord compilerURI⟩, ⟨"execution", bound.execution⟩,
    ⟨"regions", .record [("preferredRawFenceDepth", .integer 1)]⟩]⟩
  let some checked := decode? upstreamLimits (encodeRaw envelope) | .error "invalid package envelope"
  pure (Json.mkObj [("module", .str ("(module:document " ++
    CettaWireData.render (Value.Wire.encode (encodeRaw checked.val)) ++ ")"))])

@[export cetta_chr_package_v1]
def nativePackage (compilerURI : String) : String := answer (package compilerURI)

@[export cetta_chr_read_v1]
def nativeRead (source catalogue separator : String) : String := answer (read source catalogue separator)

@[export cetta_chr_verify_v1]
def nativeVerify (source packet forest identity allowance : String) : String :=
  answer (verifySource CHRPrologSyntax.description CHRPrologSyntax.selection source packet forest identity allowance)

@[export cetta_chr_prepare_v1]
def nativePrepare (wire rows separator entry : String) : String := answer (prepare wire rows separator entry)

@[export cetta_chr_observe_v1]
def nativeObserve (wire dictionary data separator : String) : String :=
  answer (observe wire dictionary data separator)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuntimeCompiler
