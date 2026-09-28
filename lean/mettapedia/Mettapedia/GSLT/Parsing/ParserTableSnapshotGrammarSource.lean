import Lean

/-!
# Import the grammar section of a TPP1 version-2 snapshot

This decoder follows the byte framing of `parser_pack_table_snapshot_v1.c`.
It retains production occurrences, terminal/nonterminal kinds, scopes, lexical
tag names and skip tags. Decision-table sections are bounded and skipped, not
verified as parser or lexer implementations. In particular importing a grammar
section does not prove that the snapshot's automata implement that grammar.

The file quotation is an explicit elaboration-time I/O boundary. The kernel
checks subsequent statements about the imported constructor data; it does not
prove the filesystem read or correspondence of this decoder with the C reader.
-/

namespace Mettapedia.GSLT.Parsing.ParserTableSnapshotGrammarSource

open Lean Elab Term

structure Symbol where
  kind : Nat
  name : String
  scope : Option String
  deriving DecidableEq, Repr

structure Production where
  label : String
  category : String
  rhs : List Symbol
  authored : Bool
  deriving DecidableEq, Repr

structure Grammar where
  syntaxDigest : String
  artifactDigest : String
  profile : String
  start : String
  authoredCount : Nat
  tags : List String
  skipTags : List Nat
  productions : List Production
  deriving DecidableEq, Repr

private structure Cursor where
  bytes : ByteArray
  position : Nat := 0

private abbrev Reader := StateT Cursor (Except String)

private def takeBytes (count : Nat) : Reader ByteArray := do
  let state ← get
  if state.position + count > state.bytes.size then
    throw "truncated TPP1 section"
  set { state with position := state.position + count }
  return state.bytes.extract state.position (state.position + count)

private def skipBytes (count : Nat) : Reader Unit := do
  let state ← get
  if state.position + count > state.bytes.size then
    throw "truncated TPP1 section"
  set { state with position := state.position + count }

private def word : Reader Nat := do
  let bytes ← takeBytes 4
  return bytes[0]!.toNat + 256 * bytes[1]!.toNat +
    65536 * bytes[2]!.toNat + 16777216 * bytes[3]!.toNat

private def text (count : Nat) : Reader String := do
  let bytes ← takeBytes count
  if bytes.data.contains 0 then throw "embedded NUL in snapshot name"
  match String.fromUTF8? bytes with
  | some value => pure value
  | none => throw "invalid UTF-8 in snapshot name"

private def framedText : Reader String := do text (← word)

private def many (count minimumWidth : Nat) (read : Reader α) : Reader (List α) := do
  let state ← get
  if state.position + count * minimumWidth > state.bytes.size then
    throw "truncated TPP1 vector"
  let mut values := #[]
  for _ in [:count] do values := values.push (← read)
  return values.toList

private def name (names : Array String) (index : Nat) : Reader String :=
  match names[index]? with
  | some value => pure value
  | none => throw "snapshot symbol index out of range"

private def readGrammar : Reader Grammar := do
  if (← text 4) != "TPP1" then throw "bad TPP1 magic"
  if (← word) != 2 then throw "unsupported TPP1 version"
  let syntaxDigest ← text 64
  let artifactDigest ← text 64
  let profile ← framedText
  let kernel ← word
  if kernel > 1 then throw "unknown parser kernel"
  let _conflicts ← word
  let tags ← many (← word) 4 framedText
  let skipTags ← many (← word) 4 word
  if skipTags.any (· >= tags.length) then throw "invalid lexical skip tag"
  let states ← word
  let transitions ← word
  let _tagCount ← word
  let accepts ← word
  let eofAccepts ← word
  skipBytes 12
  skipBytes (states * 24 + transitions * 12 + accepts * 4 + eofAccepts * 4)
  let names := (← many (← word) 4 framedText).toArray
  let start ← name names (← word)
  let terminals ← word
  let nonterminals ← word
  let productionCount ← word
  let authoredCount ← word
  if authoredCount > productionCount then throw "invalid authored production prefix"
  let rhsCount ← word
  let actions ← word
  let gotos ← word
  let glrActions ← word
  skipBytes 4
  let _terminalNames ← many terminals 4 (do name names (← word))
  let _nonterminalNames ← many nonterminals 4 (do name names (← word))
  let raw ← many productionCount 20 do
    let label ← name names (← word)
    let category ← name names (← word)
    let first ← word
    let length ← word
    let authored ← word
    if authored > 1 then throw "invalid authored flag"
    return (label, category, first, length, authored == 1)
  let rhs ← many rhsCount 12 do
    let kind ← word
    if kind > 2 then throw "unknown grammar-symbol kind"
    let symbolName ← name names (← word)
    let scopeIndex ← word
    let scope ← if scopeIndex == 4294967295 then pure none
      else some <$> name names scopeIndex
    return Symbol.mk kind symbolName scope
  let mut productions := #[]
  for (label, category, first, length, authored) in raw do
    if first + length > rhsCount then throw "production RHS slice out of range"
    productions := productions.push ⟨label, category, (rhs.drop first).take length, authored⟩
  if productions.toList.zipIdx |>.any (fun (p, i) => p.authored != (i < authoredCount)) then
    throw "authored productions are not the declared prefix"
  skipBytes (actions * 8 + gotos * 4 + 24 + glrActions * 16)
  let state ← get
  if state.position != state.bytes.size then throw "trailing TPP1 bytes"
  return ⟨syntaxDigest, artifactDigest, profile, start, authoredCount,
    tags, skipTags, productions.toList⟩

def decode (bytes : ByteArray) : Except String Grammar :=
  (readGrammar.run ⟨bytes, 0⟩).map Prod.fst

theorem empty_rejected : decode ByteArray.empty = .error "truncated TPP1 section" := by
  rfl

instance : ToExpr Symbol where
  toTypeExpr := mkConst ``Symbol
  toExpr value := mkAppN (mkConst ``Symbol.mk)
    #[toExpr value.kind, toExpr value.name, toExpr value.scope]

instance : ToExpr Production where
  toTypeExpr := mkConst ``Production
  toExpr value := mkAppN (mkConst ``Production.mk)
    #[toExpr value.label, toExpr value.category, toExpr value.rhs, toExpr value.authored]

instance : ToExpr Grammar where
  toTypeExpr := mkConst ``Grammar
  toExpr value := mkAppN (mkConst ``Grammar.mk)
    #[toExpr value.syntaxDigest, toExpr value.artifactDigest, toExpr value.profile,
      toExpr value.start, toExpr value.authoredCount, toExpr value.tags,
      toExpr value.skipTags, toExpr value.productions]

scoped syntax "parser_snapshot_grammar_file% " str : term

elab_rules : term
  | `(parser_snapshot_grammar_file% $path:str) => do
      let context ← readThe Lean.Core.Context
      let some parent := (System.FilePath.mk context.fileName).parent
        | throwErrorAt path "cannot determine source-file parent"
      let bytes ← IO.FS.readBinFile (parent / path.getString)
      match decode bytes with
      | .error message => throwErrorAt path "{message}"
      | .ok grammar => pure (toExpr grammar)

end Mettapedia.GSLT.Parsing.ParserTableSnapshotGrammarSource
