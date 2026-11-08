import Mettapedia.Languages.Lean.ParserAdapter4331

/-!
# Versioned Lean parser probes

`#parser_probe category "input" depth` exports raw syntax with source information,
the persistent declaration log and active-scope metadata at that command.
`#assert_parser_kind` checks user-facing kind names (private-name prefixes are
removed only for that assertion; exported syntax retains the exact raw names).

This is an untrusted reference producer, not a replay certificate. The
persistent declaration log omits local entries; the exported metadata does
not serialize arbitrary parser functions, macros or elaborators. The parser
is called under the current command options, namespace and open declarations.
All host API access is isolated in this version-specific module.
-/

namespace Mettapedia.Languages.Lean.ParserOracle4331

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Command
open ParserAdapter4331

def nameJson : ParserDescription.Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str parent value => Json.arr #[toJson "str", nameJson parent, toJson value]
  | .num parent value => Json.arr #[toJson "num", nameJson parent, toJson value]

/-- Explicit schema tags keep the wire independent of Lean's derived Repr. -/
def descriptionJson : ParserDescription.Description → Json
  | .constant name => Json.arr #[toJson "constant", nameJson name]
  | .unary name body => Json.arr #[toJson "unary", nameJson name, descriptionJson body]
  | .binary name left right => Json.arr #[toJson "binary", nameJson name,
      descriptionJson left, descriptionJson right]
  | .node kind prec body => Json.arr #[toJson "node", nameJson kind, toJson prec, descriptionJson body]
  | .trailingNode kind prec lhs body => Json.arr #[toJson "trailingNode", nameJson kind,
      toJson prec, toJson lhs, descriptionJson body]
  | .symbol text => Json.arr #[toJson "symbol", toJson text]
  | .nonReservedSymbol text includeIdent => Json.arr #[toJson "nonReservedSymbol", toJson text, toJson includeIdent]
  | .category name prec => Json.arr #[toJson "category", nameJson name, toJson prec]
  | .parser name => Json.arr #[toJson "parser", nameJson name]
  | .nodeWithAntiquot name kind body => Json.arr #[toJson "nodeWithAntiquot", toJson name,
      nameJson kind, descriptionJson body]
  | .sepBy body sep parser trailing => Json.arr #[toJson "sepBy", descriptionJson body,
      toJson sep, descriptionJson parser, toJson trailing]
  | .sepBy1 body sep parser trailing => Json.arr #[toJson "sepBy1", descriptionJson body,
      toJson sep, descriptionJson parser, toJson trailing]
  | .unicodeSymbol text ascii preserve => Json.arr #[toJson "unicodeSymbol", toJson text,
      toJson ascii, toJson preserve]

def packetJson (declaration : Lean.Name) (phase : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Phase)
    (description : Lean.ParserDescr) : Except String Json := do
  unless hostSupported do throw "unqualified Lean descriptor release"
  pure (Json.mkObj [("schema", toJson profile.schema), ("release", toJson profile.release),
    ("adapter", toJson profile.adapter), ("declaration", nameJson (exportName declaration)),
    ("phase", toJson (match phase with | .leading => "leading" | .trailing => "trailing")),
    ("description", descriptionJson (exportDescription description))])

def entryJson : ParserDescription.RegistryEntry → Json
  | .token text => Json.arr #[toJson "token", toJson text]
  | .kind name => Json.arr #[toJson "kind", nameJson name]
  | .category name declaration behavior => Json.arr #[toJson "category", nameJson name,
      nameJson declaration, toJson (match behavior with
        | .default => "default" | .symbol => "symbol" | .both => "both")]
  | .parser category declaration priority =>
      Json.arr #[toJson "parser", nameJson category, nameJson declaration, toJson priority]

def scopedEntryJson : ScopedEnvExtension.Entry Parser.ParserExtension.OLeanEntry → Json
  | .global entry => Json.arr #[toJson "global", entryJson (exportEntry entry)]
  | .scoped ns entry => Json.arr #[toJson "scoped", nameJson (exportName ns), entryJson (exportEntry entry)]

def infoJson : SourceInfo → Json
  | .none => toJson (["none"] : List String)
  | .original leading start trailing stop =>
      Json.arr #[toJson "original", toJson leading.toString, toJson start.byteIdx,
        toJson trailing.toString, toJson stop.byteIdx]
  | .synthetic start stop canonical =>
      Json.arr #[toJson "synthetic", toJson start.byteIdx, toJson stop.byteIdx, toJson canonical]

def preresolvedJson : Syntax.Preresolved → Json
  | .namespace ns => Json.arr #[toJson "namespace", nameJson (exportName ns)]
  | .decl name fields => Json.arr #[toJson "decl", nameJson (exportName name), toJson fields]

/-- Bounded serialization reports exhaustion explicitly; it never substitutes
a truncated syntax tree for a complete observation. -/
def syntaxJson : Nat → Syntax → Except String Json
  | 0, _ => .error "syntax serialization bound exhausted"
  | _ + 1, .missing => .ok (toJson (["missing"] : List String))
  | _ + 1, .atom info text => .ok (Json.arr #[toJson "atom", infoJson info, toJson text])
  | _ + 1, .ident info raw name resolved =>
      .ok (Json.arr #[toJson "ident", infoJson info, toJson raw.toString,
        nameJson (exportName name), Json.arr (resolved.map preresolvedJson).toArray])
  | fuel + 1, .node info kind children => do
      let encoded ← children.mapM (syntaxJson fuel)
      pure (Json.arr #[toJson "node", infoJson info, nameJson (exportName kind), Json.arr encoded])

def optionValueJson (depth : Nat) : DataValue → Except String Json
  | .ofString value => pure (Json.arr #[toJson "string", toJson value])
  | .ofBool value => pure (Json.arr #[toJson "bool", toJson value])
  | .ofName value => pure (Json.arr #[toJson "name", nameJson (exportName value)])
  | .ofNat value => pure (Json.arr #[toJson "nat", toJson value])
  | .ofInt value => pure (Json.arr #[toJson "int", toJson value])
  | .ofSyntax value => do pure (Json.arr #[toJson "syntax", ← syntaxJson depth value])

def optionsJson (depth : Nat) (options : Options) : Except String Json := do
  let mut entries := #[]
  for (name, value) in options do
    entries := entries.push (Json.arr #[nameJson (exportName name), ← optionValueJson depth value])
  pure (Json.arr entries)

def openDeclJson : OpenDecl → Json
  | .simple ns hidden => Json.arr #[toJson "simple", nameJson (exportName ns),
      Json.arr (hidden.map (nameJson ∘ exportName)).toArray]
  | .explicit id declaration =>
      Json.arr #[toJson "explicit", nameJson (exportName id), nameJson (exportName declaration)]

def parse (env : Environment) (scope : Scope) (category : Lean.Name) (input : String) : Except String Syntax :=
  let parser := Parser.andthenFn Parser.whitespace (Parser.categoryParserFnImpl category)
  let context := Parser.mkInputContext input "<parser-probe>"
  let result := parser.run context
    { env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    (Parser.getTokenTable env) (Parser.mkParserState input)
  if !result.allErrors.isEmpty then .error (result.toErrorMsg context)
  else if context.atEnd result.pos then .ok result.stxStack.back
  else .error ((result.mkError "end of input").toErrorMsg context)

def probeJson (env : Environment) (scope : Scope) (category : Lean.Name)
    (input : String) (depth : Nat) : Except String Json := do
  unless hostSupported do throw "this parser adapter has not been qualified for the running Lean release"
  let state := Parser.parserExtension.ext.getState (asyncMode := .local) env
  let active := match state.stateStack with
    | [] => []
    | head :: _ => head.activeScopes.toList
  let result ← match parse env scope category input with
    | .ok tree => do
        let value ← syntaxJson depth tree
        pure (Json.mkObj [("status", toJson "parsed"), ("syntax", value)])
    | .error error => pure (Json.mkObj [("status", toJson "refused"), ("message", toJson error)])
  pure (Json.mkObj [
    ("schema", toJson profile.schema), ("release", toJson Lean.versionString),
    ("adapter", toJson profile.adapter), ("category", nameJson (exportName category)),
    ("imports", Json.arr (env.header.imports.map fun imported => nameJson (exportName imported.module))),
    ("input", toJson input), ("namespace", nameJson (exportName scope.currNamespace)),
    ("serializationDepth", toJson depth), ("options", ← optionsJson depth scope.opts),
    ("openDeclarations", Json.arr (scope.openDecls.map openDeclJson).toArray),
    ("activeScopes", Json.arr (active.map (nameJson ∘ exportName)).toArray),
    ("scopeDepth", toJson state.stateStack.length),
    ("declarationLog", Json.arr (state.newEntries.reverse.map scopedEntryJson).toArray),
    ("result", result)])

syntax (name := exportParserProbe) "#parser_probe " ident str num : command
syntax (name := assertParserKind) "#assert_parser_kind " ident str ident : command

elab_rules : command
  | `(#parser_probe $category:ident $input:str $depth:num) => do
      let result := probeJson (← getEnv) (← getScope) category.getId input.getString depth.getNat
      match result with
      | .ok json => liftIO (IO.println json.compress)
      | .error error => throwError error
  | `(#assert_parser_kind $category:ident $input:str $kind:ident) => do
      unless hostSupported do throwError "unqualified Lean parser release"
      match parse (← getEnv) (← getScope) category.getId input.getString with
      | .error error => throwError "parser unexpectedly refused: {error}"
      | .ok tree =>
          unless privateToUserName tree.getKind == kind.getId do
            throwError "expected kind {kind.getId}, got {tree.getKind}"

end Mettapedia.Languages.Lean.ParserOracle4331
