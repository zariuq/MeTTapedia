import Mettapedia.Languages.Lean.CommandProfile4331
import Mettapedia.Languages.Lean.ParserScope4331
import Lean.Elab.Frontend

/-!
# Command-by-command reference and replay observations

The first pass parses and elaborates the source with the pinned Lean frontend.
The replay starts from the same imports and replays the recorded command syntax,
so local syntax declarations and scope effects are included even when they do
not occur in the persistent parser-extension log. Parsing under each replayed
environment is compared with the recorded syntax. The GSLT profile is compared
separately; unsupported forms may advance the reference context but are never
reported as parsed by GSLT.

Scope snapshots observe options, namespaces, open declarations, token inventories,
parser-table metadata and local boundaries. They are not an equality test for
arbitrary parser functions. Source positions are retained in records but omitted
from structural syntax comparison.
-/

namespace Mettapedia.Languages.Lean.FrontendReplay4331

open _root_.Lean _root_.Lean.Elab
open ParserOracle4331 ParserAdapter4331

structure Record where
  start : Nat
  stop : Nat
  source : String
  tree : Syntax
  before : Json
  after : Json
  tokens : List String

structure Trace where
  header : HeaderSyntax
  parserState : Parser.ModuleParserState
  records : Array Record
  finalState : Command.State

def sortedNames (names : List Name) : List Name :=
  (names.toArray.qsort (fun a b => a.toString < b.toString)).toList

def sortedStrings (names : Array String) : List String :=
  (names.qsort (· < ·)).toList

def tableObservation (table : Parser.TokenMap (Parser.Parser × Nat)) : Json :=
  Json.arr (table.toList.toArray.map fun (token, parsers) =>
    Json.arr #[nameJson (exportName token), toJson (parsers.map Prod.snd)])

def parserObservation (state : Parser.ParserExtension.State) : Json :=
  let categories := state.categories.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  Json.mkObj [
    ("tokens", toJson (sortedStrings state.tokens.values)),
    ("categories", Json.arr (categories.map fun (name, category) => Json.mkObj [
      ("name", nameJson (exportName name)), ("declaration", nameJson (exportName category.declName)),
      ("behavior", toJson (reprStr category.behavior)),
      ("kinds", Json.arr ((sortedNames (category.kinds.toList.map Prod.fst)).map (nameJson ∘ exportName)).toArray),
      ("leading", tableObservation category.tables.leadingTable),
      ("leadingUnindexed", toJson (category.tables.leadingParsers.map Prod.snd)),
      ("trailing", tableObservation category.tables.trailingTable),
      ("trailingUnindexed", toJson (category.tables.trailingParsers.map Prod.snd))]))]

def scopeObservation (state : Command.State) : Except String Json := do
  let mut scopes := #[]
  for scope in state.scopes do
    scopes := scopes.push (Json.mkObj [
      ("namespace", nameJson (exportName scope.currNamespace)), ("header", toJson scope.header),
      ("open", Json.arr (scope.openDecls.map openDeclJson).toArray),
      ("options", ← optionsJson 256 scope.opts)])
  let parserState := Parser.parserExtension.ext.getState (asyncMode := .local) state.env
  return Json.mkObj [
    ("scopes", Json.arr scopes),
    ("parserFrames", Json.arr (parserState.stateStack.toArray.map fun frame => Json.mkObj [
      ("boundary", toJson frame.delimitsLocal),
      ("active", Json.arr ((sortedNames frame.activeScopes.toList).map (nameJson ∘ exportName)).toArray),
      ("grammar", parserObservation frame.state)])),
    ("published", Json.arr (parserState.newEntries.reverse.map scopedEntryJson).toArray)]

def requireObservation (state : Command.State) : IO Json := IO.ofExcept (scopeObservation state)

def requireNoErrors (phase : String) (messages : MessageLog) : IO Unit := do
  if messages.hasErrors then
    let details ← messages.toList.mapM fun message => message.toString
    throw (IO.userError (phase ++ ":\n" ++ String.intercalate "\n" details))

def sourceSlice (input : String) (start stop : String.Pos.Raw) : String :=
  ({ str := input, startPos := start, stopPos := stop } : Substring.Raw).toString

def captureCommands : Frontend.FrontendM (Array Record) := do
  let context ← Frontend.getInputContext
  let mut records := #[]
  for _ in [0:context.inputString.utf8ByteSize + 1] do
    Frontend.updateCmdPos
    let beforeState ← Frontend.getCommandState
    let before ← requireObservation beforeState
    let parserState ← Frontend.getParserState
    let some scope := beforeState.scopes.head? | throw (IO.userError "no command scope")
    let parseContext : Parser.ParserModuleContext := {
      env := beforeState.env
      options := scope.opts
      currNamespace := scope.currNamespace
      openDecls := scope.openDecls }
    let (tree, afterParser, messages) := Parser.parseCommand context parseContext parserState beforeState.messages
    requireNoErrors "reference parser" messages
    Frontend.setParserState afterParser
    Frontend.setMessages messages
    if Parser.isTerminalCommand tree then return records
    unless afterParser.pos.byteIdx > parserState.pos.byteIdx do
      throw (IO.userError "reference parser made no progress")
    let start := tree.getPos?.getD parserState.pos
    let stop := tree.getTailPos?.getD afterParser.pos
    Frontend.elabCommandAtFrontend tree
    let afterState ← Frontend.getCommandState
    requireNoErrors "reference elaboration" afterState.messages
    records := records.push {
      start := start.byteIdx, stop := stop.byteIdx, source := sourceSlice context.inputString start stop,
      tree, before, after := ← requireObservation afterState,
      tokens := sortedStrings (Parser.getTokenTable beforeState.env).values }
  throw (IO.userError "command capture exhausted its progress allowance")

def initialState (input : String) (mainModule : Name) : IO (Parser.InputContext × HeaderSyntax × Frontend.State) := do
  unless hostSupported do throw (IO.userError "unqualified Lean frontend release")
  let context := Parser.mkInputContext input "<frontend-profile>"
  let (header, parserState, messages) ← Parser.parseHeader context
  requireNoErrors "header parser" messages
  -- Importing resets this host flag. Each independent replay imports afresh.
  unsafe enableInitializersExecution
  let (env, messages) ← processHeader header {} messages context (mainModule := mainModule)
  requireNoErrors "import processing" messages
  return (context, header, { commandState := Command.mkState env messages {}, parserState, cmdPos := parserState.pos })

def capture (input : String) (mainModule : Name) : IO Trace := do
  let (context, header, initial) ← initialState input mainModule
  let (records, final) ← (captureCommands { inputCtx := context }).run initial
  return ⟨header, initial.parserState, records, final.commandState⟩

def kinds : Nat → Syntax → List Name
  | 0, _ => []
  | depth + 1, .node _ kind children => kind :: children.toList.flatMap (kinds depth)
  | _, _ => []

/-- The names in this allowlist are implemented by the pinned realization.
Unlisted source nodes are exposed individually, including nodes inside tactic
blocks and extensions introduced by notation declarations. -/
def implementedKinds : List String := [
  "null", "Lean.Parser.Command.namespace", "Lean.Parser.Command.section",
  "Lean.Parser.Command.sectionHeader", "Lean.Parser.Command.end", "Lean.Parser.Command.open",
  "Lean.Parser.Command.openSimple", "Lean.Parser.Command.openScoped", "Lean.Parser.Module.import",
  "Lean.Parser.Command.moduleDoc", "Lean.Parser.Command.declaration", "Lean.Parser.Command.declModifiers",
  "Lean.Parser.Command.docComment", "Lean.Parser.Command.abbrev", "Lean.Parser.Command.inductive",
  "Lean.Parser.Command.structure", "Lean.Parser.Command.structureTk", "Lean.Parser.Command.structFields",
  "Lean.Parser.Command.structSimpleBinder", "Lean.Parser.Command.ctor", "Lean.Parser.Command.declId",
  "Lean.Parser.Command.optDeclSig", "Lean.Parser.Command.declValSimple", "Lean.Parser.Command.optDeriving",
  "Lean.Parser.Command.derivingClass", "Lean.Parser.Termination.suffix", "Lean.Parser.Term.typeSpec",
  "Lean.Parser.Term.prop", "Lean.Parser.Term.type", "Lean.Parser.Term.arrow", "Lean.Parser.Term.app",
  "Lean.Parser.Term.paren", "Lean.Parser.Term.hygienicLParen", "hygieneInfo"]

/-- Unsupported forms do not consume a parser budget. This is a coverage
classification, not an acceptance or refusal result from the GSLT parser. -/
def missingMechanisms (tree : Syntax) : List String :=
  ((kinds 512 tree).eraseDups.map toString).filterMap fun name =>
    if implementedKinds.contains name then none else some ("syntax production: " ++ name)

def compareRecord (record : Record) : IO Json := do
  let fuel := 3 * record.source.toList.length + 32
  let missing := missingMechanisms record.tree
  let parsed := if missing.isEmpty then
    Mettapedia.GSLT.Parsing.LeanCommandProfile.parse record.tokens record.source fuel else []
  let mut matched := false
  let mut mismatches := 0
  for candidate in parsed do
    if ← IO.ofExcept (CommandProfile4331.compare 512 record.tree candidate) then matched := true
    else mismatches := mismatches + 1
  if mismatches != 0 then
    throw (IO.userError s!"GSLT invented a different syntax tree at byte {record.start}")
  if !matched && missing.isEmpty then
    throw (IO.userError s!"unclassified profile omission at byte {record.start}: {record.source}")
  return Json.mkObj [
    ("start", toJson record.start), ("stop", toJson record.stop), ("source", toJson record.source),
    ("kind", toJson record.tree.getKind.toString), ("status", toJson (if matched then "matched" else "unmatched")),
    ("fuel", toJson fuel), ("candidates", toJson parsed.length), ("mismatches", toJson mismatches),
    ("missingMechanisms", toJson missing),
    ("syntaxKinds", toJson ((kinds 512 record.tree).eraseDups.map toString)),
    ("scopeChanged", toJson (record.before != record.after))]

def replayCommands (records : Array Record) : Frontend.FrontendM (Array Json) := do
  let mut output := #[]
  for record in records do
    let beforeState ← Frontend.getCommandState
    unless (← requireObservation beforeState) == record.before do
      throw (IO.userError s!"grammar state diverged before byte {record.start}")
    let some scope := beforeState.scopes.head? | throw (IO.userError "missing replay scope")
    let replayed ← IO.ofExcept (ParserOracle4331.parse beforeState.env scope `command record.source)
    unless (← IO.ofExcept (CommandProfile4331.observation 512 replayed)) ==
        (← IO.ofExcept (CommandProfile4331.observation 512 record.tree)) do
      throw (IO.userError s!"native syntax changed under replay at byte {record.start}")
    output := output.push (← compareRecord record)
    modify fun state => { state with cmdPos := ⟨record.start⟩ }
    Frontend.elabCommandAtFrontend record.tree
    let afterState ← Frontend.getCommandState
    requireNoErrors "replayed elaboration" afterState.messages
    unless (← requireObservation afterState) == record.after do
      throw (IO.userError s!"grammar state diverged after byte {record.stop}")
  return output

def qualify (input : String) (mainModule : Name) : IO Json := do
  let trace ← capture input mainModule
  let (context, replayHeader, initial) ← initialState input mainModule
  unless (← IO.ofExcept (CommandProfile4331.observation 512 trace.header.raw)) ==
      (← IO.ofExcept (CommandProfile4331.observation 512 replayHeader.raw)) do
    throw (IO.userError "import header changed under replay")
  let headerSnapshot ← requireObservation initial.commandState
  let headerTokens := sortedStrings (Parser.Module.updateTokens (Parser.getTokenTable initial.commandState.env)).values
  let mut headers := #[]
  for tree in trace.header.raw[2].getArgs do
    let some start := tree.getPos? | throw (IO.userError "import has no start position")
    let some stop := tree.getTailPos? | throw (IO.userError "import has no stop position")
    headers := headers.push (← compareRecord {
      start := start.byteIdx, stop := stop.byteIdx, source := sourceSlice input start stop,
      tree, before := headerSnapshot, after := headerSnapshot, tokens := headerTokens })
  let (rows, _) ← (replayCommands trace.records { inputCtx := context }).run initial
  return Json.mkObj [
    ("lean", toJson Lean.versionString), ("schema", toJson (2 : Nat)),
    ("module", nameJson (exportName mainModule)), ("header", Json.arr headers), ("commands", Json.arr rows),
    ("scopeReplay", toJson "all recorded before/after observations equal; imports replayed from fresh state"),
    ("framing", toJson "reference frontend supplies command boundaries and elaborated context updates"),
    ("comparison", toJson "bounded GSLT grammar; full syntax structure except source positions"),
    ("evidence", toJson "differential qualification; not a general Lean parser equivalence proof")]

end Mettapedia.Languages.Lean.FrontendReplay4331
