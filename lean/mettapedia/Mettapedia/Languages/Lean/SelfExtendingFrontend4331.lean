import Mettapedia.Languages.Lean.ParserHostEffects4331
import Mettapedia.GSLT.Parsing.PresentationNative
import Mettapedia.Languages.Lean.CompiledParserSelection

/-!
# Native GSLT command-stream driver

Candidate command spans come from the authored GSLT stream grammar. Native
certificates are replayed before lexical filtering and syntax readback. The
Lean parser is used only by the optional comparison gate, after the candidate
has been selected; it never supplies the stream cursor or an input slice.
-/

namespace Mettapedia.Languages.Lean.SelfExtendingFrontend4331

open _root_.Lean _root_.Lean.Elab
open Mettapedia.GSLT.Parsing
open PresentationExprSemantics

structure Parsed where
  stop : Nat
  tree : CST
  command : LeanSyntaxReadback4331.Command
  syntaxTree : Syntax

/-- Expand retained choice nodes only for checking membership in the native
forest. Readback itself keeps the choices at their original nested positions. -/
def expansions : Nat → Syntax → Except String (List Syntax)
  | 0, _ => .error "choice membership budget exhausted"
  | fuel + 1, .node info kind args => do
      let children ← args.toList.mapM (expansions fuel)
      if kind == choiceKind then return children.flatten
      let products := children.foldr (fun alternatives tails =>
        alternatives.flatMap fun head => tails.map (head :: ·)) [[]]
      return products.map fun children => .node info kind children.toArray
  | _, syntaxTree => pure [syntaxTree]

def selection (state : ParserHostEffects4331.State) (input : String) (rows : List LeanSyntaxBootstrap.DynamicRow)
    (candidates : Array PresentationNative.Candidate) : Except String (Option Parsed) := do
  let some top := state.target.frames.head? | throw "missing compiled grammar scope"
  let tokens := state.baseTokens ++ top.value.tokens
  let scalars := input.toList.map Char.toNat
  let mut parsed : List Parsed := []
  for candidate in candidates do
    let [tree@(.node _ _ stop _)] := candidate.output | throw "command grammar returned the wrong root shape"
    unless LeanSyntaxReadback4331.lexical tokens scalars tree do continue
    let command ← LeanSyntaxReadback4331.readCommand tree
    let syntaxTree ← LeanSyntaxReadback4331.commandSyntax rows command
    parsed := parsed ++ [⟨stop, tree, command, syntaxTree⟩]
  if let some first := parsed.head? then
    if let .check term := first.command then
      let start := match term with | .node _ start .. | .terminal _ start _ => start
      let budget := scalars.length * 8 + 256
      let result ← CompiledParserSelection.category ⟨rows, tokens, scalars⟩ budget 0 start
      unless result.succeeded do return none
      let [selectedTerm] := result.output | throw "parser policy returned the wrong term shape"
      let selected ← LeanSyntaxReadback4331.commandSyntax rows (.check selectedTerm)
      let alternatives ← expansions budget selected
      if alternatives.isEmpty then throw "parser policy produced an empty choice"
      let retained := parsed.filter (·.stop == result.stop)
      let observations ← retained.mapM fun candidate => CommandProfile4331.observation budget candidate.syntaxTree
      for alternative in alternatives do
        let observed ← CommandProfile4331.observation budget alternative
        unless observations.contains observed do
          throw "parser policy result has no replayed GSLT derivation"
      let some witness := retained.head? | throw "parser policy endpoint has no replayed GSLT derivation"
      return some { witness with command := .check selectedTerm, syntaxTree := selected }
  let mut selected : Option Parsed := none
  let mut observation : Option Json := none
  for candidate in parsed do
    let current ← CommandProfile4331.observation (LeanSyntaxReadback4331.treeDepth candidate.tree + 64) candidate.syntaxTree
    match selected with
    | none =>
        selected := some candidate
        observation := some current
    | some previous =>
        if previous.stop < candidate.stop then
          selected := some candidate
          observation := some current
        else if previous.stop == candidate.stop && observation != some current then
          throw "command alternatives require an additional declared selection policy"
  return selected

def reference (state : ParserHostEffects4331.State) (input : String) (isImport : Bool) : IO Syntax := do
  let scope ← ParserHostEffects4331.scope state.host
  let context := Parser.mkInputContext input "<lean-reference>"
  if isImport then
    let (header, _, messages) ← Parser.parseHeader context
    FrontendReplay4331.requireNoErrors "reference import parser" messages
    let some first := header.raw[2].getArgs[0]? | throw (IO.userError "reference header has no import")
    return first
  let parseContext : Parser.ParserModuleContext := {
    env := state.host.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls }
  let (tree, _, messages) := Parser.parseCommand context parseContext {} {}
  FrontendReplay4331.requireNoErrors "reference parser" messages
  return tree

/-- Negative fixtures end in term observations. Lean may accept a shorter
`#check` and report the error at the following token as a new command. Inspect
that remaining stream, without using its boundaries in the GSLT execution. -/
def referenceRefusesTail (state : ParserHostEffects4331.State) (input : String) : IO Bool := do
  let scope ← ParserHostEffects4331.scope state.host
  let context := Parser.mkInputContext input "<lean-negative-reference>"
  let parseContext : Parser.ParserModuleContext := {
    env := state.host.env, options := scope.opts,
    currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let mut cursor : Parser.ModuleParserState := {}
  for _ in [:input.utf8ByteSize + 1] do
    let (tree, next, messages) := Parser.parseCommand context parseContext cursor {}
    if messages.hasErrors then return true
    if context.atEnd next.pos then return false
    unless tree.getKind == `Lean.Parser.Command.check do
      throw (IO.userError "negative fixture has an unexecuted grammar-changing command")
    unless cursor.pos.byteIdx < next.pos.byteIdx do
      throw (IO.userError "reference negative check did not advance")
    cursor := next
  throw (IO.userError "reference negative check exhausted its progress allowance")

def run (config : PresentationNative.Config) (mainModule : _root_.Lean.Name) (input : String)
    (compareReference := true) (expectRefusal := false) : IO Json := do
  let mut state ← ParserHostEffects4331.initial mainModule
  let original := input.toList
  let mut cursor := 0
  let mut records := #[]
  for commandNumber in [:original.length + 1] do
    let remaining := String.ofList (original.drop cursor)
    let (presentation, rows) ← IO.ofExcept (LeanSyntaxBootstrap.materialize state.source state.target)
    let candidates ← PresentationNative.run config ("command-" ++ toString commandNumber)
      presentation LeanSyntaxBootstrap.profile "front.command" remaining
    let parsed ← IO.ofExcept (selection state remaining rows candidates)
    match parsed with
    | none =>
        let endings ← PresentationNative.run config ("end-" ++ toString commandNumber)
          presentation LeanSyntaxBootstrap.profile "front.end" remaining
        if endings.isEmpty then
          if expectRefusal && compareReference then
            unless ← referenceRefusesTail state remaining do
              throw (IO.userError "GSLT refused but Lean accepted the negative fixture")
            return Json.mkObj [("lean", toJson Lean.versionString), ("backend", toJson config.backend),
              ("commands", Json.arr records), ("status", toJson "refused"),
              ("refusalStart", toJson cursor), ("reference", toJson "refused")]
          throw (IO.userError s!"GSLT refused the command at scalar {cursor}")
        if expectRefusal then throw (IO.userError "negative fixture was accepted")
        return Json.mkObj [("lean", toJson Lean.versionString), ("backend", toJson config.backend),
          ("commands", Json.arr records), ("status", toJson "complete"),
          ("framing", toJson "GSLT command spans; no Lean-supplied boundaries")]
    | some parsed =>
        unless 0 < parsed.stop && cursor + parsed.stop ≤ original.length do
          throw (IO.userError "command did not make bounded progress")
        if compareReference then
          let isImport := match parsed.command with | .existing (.import_ _) => true | _ => false
          let expected ← reference state remaining isImport
          let observed ← IO.ofExcept (CommandProfile4331.observation (remaining.length + 256) parsed.syntaxTree)
          let expected ← IO.ofExcept (CommandProfile4331.observation (remaining.length + 256) expected)
          unless observed == expected do
            throw (IO.userError ("GSLT syntax differs from Lean: " ++ observed.compress ++ "\nexpected: " ++ expected.compress))
        state ← ParserHostEffects4331.applyCommand state parsed.command parsed.syntaxTree remaining
        records := records.push (Json.mkObj [("start", toJson cursor), ("stop", toJson (cursor + parsed.stop)),
          ("kind", toJson parsed.syntaxTree.getKind.toString),
          ("syntax", ← IO.ofExcept (CommandProfile4331.observation (remaining.length + 256) parsed.syntaxTree))])
        cursor := cursor + parsed.stop
  throw (IO.userError "command stream exhausted its progress allowance")

end Mettapedia.Languages.Lean.SelfExtendingFrontend4331
