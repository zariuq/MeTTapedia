import Mettapedia.GSLT.Parsing.IntegerProviderNativeTypeExport
import Lean

/-!
# Quoting the existing textual ParserPack ABI

Only ABI framing is read here. Production expressions use the existing PeTTa
S-expression reader; no source-language parser, NFA executor or guard oracle is
introduced. Physical production order, ABI line coordinates and complete raw
fields are retained. Digests identify artifacts and do not prove semantics.

File quotation is an elaboration-time I/O boundary. Subsequent proofs check
the imported constructor data in the kernel; quotation does not establish
that the native reader or parser implements this data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserPackTextArtifact

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Lean Elab Term

structure Row where
  line : Nat
  tag : String
  fields : List String
  deriving DecidableEq, Repr

structure Artifact where
  text : String
  rows : List Row
  productions : List SExpr
  deriving DecidableEq, Repr

def rowsFor (artifact : Artifact) (tag : String) : List Row :=
  artifact.rows.filter fun row => row.tag == tag

def uniqueField? (artifact : Artifact) (tag : String) : Option String :=
  match (rowsFor artifact tag).map Row.fields with
  | [[field]] => some field
  | _ => none

private def readRows (lines : List String) : Except String (List Row) := do
  let mut rows := []
  let mut lineNumber := 0
  for line in lines do
    lineNumber := lineNumber + 1
    match line.splitOn "\t" with
    | tag :: fields => rows := ⟨lineNumber, tag, fields⟩ :: rows
    | [] => throw "invalid empty ABI row"
  pure rows.reverse

private def recognized (row : Row) : Bool :=
  match row.tag, row.fields with
  | "parser-pack-abi-v1", [] | "end", [] => true
  | "source-digest", [_] | "compiler-digest", [_] |
      "environment-digest", [_] | "pack-digest", [_] |
      "start", [_] | "closure", [_] | "production", [_] |
      "class-clause", [_] => true
  | "production-evidence", [_, _, _] | "class-evidence", [_, _, _] => true
  | _, _ => false

/-- ABI framing, with unknown or repeated header fields refused. Evidence
fields remain exact text; they are not interpreted as semantic proofs. -/
def read (text : String) : Except String Artifact := do
  let lines := text.splitOn "\n"
  let lines := if lines.getLast? = some "" then lines.dropLast else lines
  let rows ← readRows lines
  if rows.head?.map Row.tag != some "parser-pack-abi-v1" then throw "bad ParserPack ABI header"
  if rows.getLast?.map Row.tag != some "end" then throw "bad ParserPack ABI terminator"
  if !(rows.all recognized) then throw "unknown or malformed ParserPack ABI row"
  let artifact : Artifact := ⟨text, rows, []⟩
  for header in ["parser-pack-abi-v1", "end", "source-digest", "compiler-digest",
      "environment-digest", "pack-digest", "start", "closure"] do
    if (rowsFor artifact header).length != 1 then throw "repeated or missing ParserPack ABI header"
  if uniqueField? artifact "closure" != some "partial" &&
      uniqueField? artifact "closure" != some "closed" then throw "unknown ParserPack closure"
  let productions ← (rowsFor artifact "production").mapM fun row =>
    match row.fields with
    | [field] => IntegerProviderNativeTypeExport.parseSource field
    | _ => .error "malformed physical production row"
  pure { artifact with productions }

private def quoteList (type : Expr) : List Expr → Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) type
  | first :: rest => mkAppN (mkConst ``List.cons [Level.zero])
      #[type, first, quoteList type rest]

private partial def quoteSExpr : SExpr → Expr
  | .atom token => mkApp (mkConst ``SExpr.atom) (toExpr token)
  | .list terms => mkApp (mkConst ``SExpr.list)
      (quoteList (mkConst ``SExpr) (terms.map quoteSExpr))

private def quoteRow (row : Row) : Expr :=
  mkAppN (mkConst ``Row.mk) #[toExpr row.line, toExpr row.tag, toExpr row.fields]

private def quoteArtifact (artifact : Artifact) : Expr :=
  mkAppN (mkConst ``Artifact.mk) #[toExpr artifact.text,
    quoteList (mkConst ``Row) (artifact.rows.map quoteRow),
    quoteList (mkConst ``SExpr) (artifact.productions.map quoteSExpr)]

scoped syntax "parser_pack_text_file% " str : term

elab_rules : term
  | `(parser_pack_text_file% $path:str) => do
      let context ← readThe Lean.Core.Context
      let some parent := (System.FilePath.mk context.fileName).parent
        | throwErrorAt path "cannot determine source-file parent"
      let contents ← IO.FS.readFile (parent / path.getString)
      match read contents with
      | .error message => throwErrorAt path "{message}"
      | .ok artifact => pure (quoteArtifact artifact)

theorem duplicate_header_refused :
    uniqueField? ⟨"", [⟨1, "start", ["A"]⟩, ⟨2, "start", ["B"]⟩], []⟩ "start" =
      none := rfl

theorem malformed_row_refused :
    recognized ⟨2, "production", ["(A)", "(B)"]⟩ = false := rfl

end Mettapedia.GSLT.Parsing.ParserPackTextArtifact
