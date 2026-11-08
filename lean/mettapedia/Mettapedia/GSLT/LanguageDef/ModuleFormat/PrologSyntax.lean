import Mettapedia.Logic.Prolog.ReaderProfile
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxNativePlan
import Mettapedia.GSLT.LanguageDef.ModuleSource.Printer

/-! Compositional Prolog sentence grammars. The shared structural grammar,
the reader profile and the current operator table are separate inputs.
Operator declarations generate ordinary grammar rows, using their x/y
precedence constraints. A source loader must rebuild these rows after a
read-time operator update. These are source constructors, not execution rules.

The present lexical admission uses ASCII unquoted identifiers and named
escapes and numeric character escapes. Full Unicode identifier classes,
SWI dicts,
rationals and quasiquotations remain outside this declared sentence surface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.Prolog ReaderProfile ReaderOperator
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

private def n (sort : String) : Sum String String := .inr sort
private def t (text : String) : Sum String String := .inl text

def row (label category : String) (items : List (Sum String String)) : GrammarRule :=
  let indexed := items.zipIdx
  { label := "pl:" ++ label, category
    params := indexed.filterMap fun (item, i) => match item with
      | .inl _ => none | .inr sort => some (.simple ("a" ++ toString i) (.base sort))
    syntaxPattern := indexed.map fun (item, i) => match item with
      | .inl text => .terminal text | .inr _ => .nonTerminal ("a" ++ toString i) }

def commonRows : List GrammarRule := [
  row "sentence" "PlSentence" [n "PlLayout", n "PlExpr1200", n "PlLayout", t ".", n "PlLayout"],
  row "layout-empty" "PlLayout" [],
  row "layout-space" "PlLayout" [n "PlSpace", n "PlLayout"],
  row "layout-line" "PlLayout" [t "%", n "PlLine", t "\n", n "PlLayout"],
  row "layout-line-end" "PlLayout" [t "%", n "PlLine"],
  row "layout-block" "PlLayout" [t "/*", n "PlComment", n "PlLayout"],
  row "comment-more" "PlComment" [n "PlCommentScalar", n "PlComment"],
  row "comment-star" "PlComment" [t "*", n "PlCommentStar"],
  row "comment-end" "PlCommentStar" [t "/"],
  row "comment-stars" "PlCommentStar" [t "*", n "PlCommentStar"],
  row "comment-after-star" "PlCommentStar" [n "PlCommentAfterStar", n "PlComment"],
  row "line-empty" "PlLine" [], row "line-more" "PlLine" [n "PlLineScalar", n "PlLine"],
  row "name-tail-empty" "PlNameTail" [], row "name-tail-more" "PlNameTail" [n "PlNameRest", n "PlNameTail"],
  row "word" "PlWord" [n "PlLower", n "PlNameTail"],
  row "variable-name" "PlVariableName" [n "PlVariableStart", n "PlNameTail"],
  row "graphic-one" "PlGraphicWord" [n "PlGraphic"],
  row "graphic-more" "PlGraphicWord" [n "PlGraphic", n "PlGraphicWord"],
  row "atom-word" "PlAtom" [n "PlWord"], row "atom-graphic" "PlAtom" [n "PlGraphicWord"],
  row "atom-quoted" "PlAtom" [t "'", n "PlSingleBody", t "'"],
  row "atom-cut" "PlAtom" [t "!"], row "atom-semicolon" "PlAtom" [t ";"],
  row "single-empty" "PlSingleBody" [],
  row "single-more" "PlSingleBody" [n "PlSingleScalar", n "PlSingleBody"],
  row "single-escape" "PlSingleBody" [t "\\", n "PlEscape", n "PlSingleBody"],
  row "escape-named" "PlEscape" [n "PlEscapeScalar"],
  row "escape-hex-code" "PlEscape" [t "x", n "PlHexDigits", t "\\"],
  row "escape-octal-code" "PlEscape" [n "PlOctDigits", t "\\"],
  row "single-double" "PlSingleBody" [t "''", n "PlSingleBody"],
  row "double-empty" "PlDoubleBody" [],
  row "double-more" "PlDoubleBody" [n "PlDoubleScalar", n "PlDoubleBody"],
  row "double-escape" "PlDoubleBody" [t "\\", n "PlEscape", n "PlDoubleBody"],
  row "double-double" "PlDoubleBody" [t "\"\"", n "PlDoubleBody"],
  row "digits-one" "PlDigits" [n "PlDigit"], row "digits-more" "PlDigits" [n "PlDigit", n "PlDigits"],
  row "hex-one" "PlHexDigits" [n "PlHex"], row "hex-more" "PlHexDigits" [n "PlHex", n "PlHexDigits"],
  row "oct-one" "PlOctDigits" [n "PlOct"], row "oct-more" "PlOctDigits" [n "PlOct", n "PlOctDigits"],
  row "bin-one" "PlBinDigits" [n "PlBin"], row "bin-more" "PlBinDigits" [n "PlBin", n "PlBinDigits"],
  row "integer" "PlNumber" [n "PlDigits"], row "hex" "PlNumber" [t "0x", n "PlHexDigits"],
  row "oct" "PlNumber" [t "0o", n "PlOctDigits"], row "bin" "PlNumber" [t "0b", n "PlBinDigits"],
  row "character-code" "PlNumber" [t "0'", n "PlCodeScalar"],
  row "character-escape" "PlNumber" [t "0'\\", n "PlEscape"],
  row "float" "PlNumber" [n "PlDigits", t ".", n "PlDigits"],
  row "float-exponent" "PlNumber" [n "PlDigits", t ".", n "PlDigits", n "PlExponent"],
  row "exponent-lower" "PlExponent" [t "e", n "PlSignedDigits"],
  row "exponent-upper" "PlExponent" [t "E", n "PlSignedDigits"],
  row "exponent-positive" "PlSignedDigits" [t "+", n "PlDigits"],
  row "exponent-negative" "PlSignedDigits" [t "-", n "PlDigits"],
  row "exponent-unsigned" "PlSignedDigits" [n "PlDigits"],
  row "term-atom" "PlExpr0" [n "PlAtom"], row "term-variable" "PlExpr0" [n "PlVariableName"],
  row "term-number" "PlExpr0" [n "PlNumber"],
  row "term-negative" "PlExpr0" [t "-", n "PlNumber"],
  row "term-text" "PlExpr0" [t "\"", n "PlDoubleBody", t "\""],
  row "term-compound" "PlExpr0" [n "PlAtom", t "(", n "PlLayout", n "PlArguments", n "PlLayout", t ")"],
  row "term-parens" "PlExpr0" [t "(", n "PlLayout", n "PlExpr1200", n "PlLayout", t ")"],
  row "term-nil" "PlExpr0" [t "[", n "PlLayout", t "]"],
  row "term-list" "PlExpr0" [t "[", n "PlLayout", n "PlArguments", n "PlLayout", t "]"],
  row "term-list-tail" "PlExpr0" [t "[", n "PlLayout", n "PlArguments", n "PlLayout", t "|",
    n "PlLayout", n "PlExpr999", n "PlLayout", t "]"],
  row "term-braces-empty" "PlExpr0" [t "{", n "PlLayout", t "}"],
  row "term-braces" "PlExpr0" [t "{", n "PlLayout", n "PlExpr1200", n "PlLayout", t "}"],
  row "arguments-one" "PlArguments" [n "PlExpr999"],
  row "arguments-more" "PlArguments" [n "PlExpr999", n "PlLayout", t ",", n "PlLayout", n "PlArguments"] ]

def extensionRows (profile : Profile) : List GrammarRule :=
  (if profile.dialect == .swi then [
    row "escape-hex-open" "PlEscape" [n "PlOpenHexEscape"],
    row "open-hex-code" "PlOpenHexEscape" [t "x", n "PlHexDigits"],
    row "escape-octal-open" "PlEscape" [n "PlOpenOctEscape"],
    row "open-octal-code" "PlOpenOctEscape" [n "PlOctDigits"],
    row "escape-unicode-four" "PlEscape" (t "u" :: List.replicate 4 (n "PlHex")),
    row "escape-unicode-eight" "PlEscape" (t "U" :: List.replicate 8 (n "PlHex"))] else []) ++
  (if profile.zeroArityCompounds then
    [row "term-zero-arity" "PlExpr0" [n "PlAtom", t "(", n "PlLayout", t ")"]] else []) ++
  (if profile.backQuotes.isSome then [
    row "term-backtext" "PlExpr0" [t "`", n "PlBackBody", t "`"],
    row "back-empty" "PlBackBody" [],
    row "back-more" "PlBackBody" [n "PlBackScalar", n "PlBackBody"],
    row "back-escape" "PlBackBody" [t "\\", n "PlEscape", n "PlBackBody"],
    row "back-double" "PlBackBody" [t "``", n "PlBackBody"]] else []) ++
  (if profile.digitSeparators then
    [row "digits-separator" "PlDigits" [n "PlDigit", t "_", n "PlDigits"]] else [])

def levels (table : Table) : List Nat :=
  (0 :: 999 :: 1200 :: table.map (·.priority.value)).eraseDups.mergeSort (· ≤ ·)

def exprSort (level : Nat) : String := "PlExpr" ++ toString level
def below (table : Table) (priority : Nat) : Nat :=
  ((levels table).filter (· < priority)).getLast?.getD 0

def operatorRows (profile : Profile) : List GrammarRule :=
  let table := profile.operators
  let lifts := ((levels table).filter (· != 0)).map fun p =>
    row ("level:" ++ toString p) (exprSort p) [n (exprSort (below table p))]
  let operators := table.zipIdx |>.flatMap fun (op, index) =>
    let label := "operator:" ++ toString index
    let token := "PlOperator" ++ toString index
    let p := op.priority.value
    let low := exprSort (below table p)
    let high := exprSort p
    let afterToken := if op.name == "." then [] else [n "PlLayout"]
    let items := match op.specifier with
      | .fx => [n token, n "PlLayout", n low]
      | .fy => [n token, n "PlLayout", n high]
      | .xf => [n low, n "PlLayout", n token]
      | .yf => [n high, n "PlLayout", n token]
      | .xfx => [n low, n "PlLayout", n token] ++ afterToken ++ [n low]
      | .xfy => [n low, n "PlLayout", n token] ++ afterToken ++ [n high]
      | .yfx => [n high, n "PlLayout", n token] ++ afterToken ++ [n low]
    [row ("apply:" ++ toString index) high items] ++
      (if bareAtom op.name || [",","|"].contains op.name then [row label token [t op.name]] else []) ++
      (if profile.quotedOperator op.name then
        [row (label ++ ":quoted") token [t ("'" ++ (op.name.replace "\\" "\\\\").replace "'" "''" ++ "'")]] else [])
  lifts ++ operators

def rows (profile : Profile) := commonRows ++ extensionRows profile ++ operatorRows profile

def sorts (rows : List GrammarRule) : List String :=
  (rows.flatMap fun row => row.category :: row.params.filterMap fun
    | .simple _ (.base sort) => some sort | _ => none).eraseDups

def grammar (profile : Profile) : LanguageDef := {
  name := if profile.dialect == .iso then "ISOPrologSentence" else "SWIPrologSentence"
  types := sorts (rows profile), terms := rows profile, equations := [], rewrites := [] }

private def points (sort : String) (chars : String) : String × LexicalClassKind :=
  (sort, .points ((chars.toList.map Char.toNat).eraseDups.mergeSort (· ≤ ·)))

def classes (profile : Profile) : List (String × LexicalClassKind) :=
  let forbidden := if profile.dialect == .iso then List.range 32 ++ (List.range 33).map (· + 127) else []
  [points "PlSpace" " \t\n\r\u000b\u000c", points "PlLower" "abcdefghijklmnopqrstuvwxyz",
   points "PlVariableStart" "ABCDEFGHIJKLMNOPQRSTUVWXYZ_",
   points "PlNameRest" "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789",
   points "PlGraphic" "#$&*+-./:<=>?@\\^~", points "PlDigit" "0123456789",
   points "PlHex" "0123456789abcdefABCDEF", points "PlOct" "01234567", points "PlBin" "01",
   points "PlEscapeScalar" ("abfnrtv\\'\"`" ++ if profile.dialect == .swi then "es" else ""),
   ("PlLineScalar", .except [10]), ("PlCommentScalar", .except [42]),
   ("PlCommentAfterStar", .except [42,47]), ("PlCodeScalar", .except [92]),
   ("PlSingleScalar", .except (([39, 92] ++ forbidden).mergeSort (· ≤ ·))),
   ("PlDoubleScalar", .except (([34, 92] ++ forbidden).mergeSort (· ≤ ·)))] ++
   (if profile.backQuotes.isSome then [("PlBackScalar", .except [92, 96])] else [])

def lexical (profile : Profile) : ParserProfileLayer := {
  name := (grammar profile).name ++ "Lexical", startSort := "PlSentence"
  classes := (classes profile).map fun (name, kind) => ⟨name, kind⟩
  states := (classes profile).map fun (sort, _) => ⟨sort, sort, "pl:scalar:" ++ sort⟩ }

def description (profile : Profile) : Portable.SyntaxDescription := ⟨grammar profile, lexical profile⟩

/-- Extend the source grammar without changing the term reader's dialect,
operator interpretation or lexical classes. Program-level frontends can
reuse the sentence constructors and choose their own root sort. -/
def extended (profile : Profile) (extra : List GrammarRule) (start name : String) :
    Portable.SyntaxDescription :=
  let allRows := rows profile ++ extra
  ⟨{ grammar profile with name, types := sorts allRows, terms := allRows },
   { lexical profile with name := name ++ "Lexical", startSort := start }⟩

theorem extended_retains_rows (profile : Profile) (extra : List GrammarRule) (start name : String) :
    (grammar profile).terms ⊆ (extended profile extra start name).grammar.terms := by
  intro rule present
  exact List.mem_append_left _ present

def selection (profile : Profile) : List SourceSyntax.FamilyFilter :=
  let rest := "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789".toList.map Char.toNat
  let graphics := "#$&*+-./:<=>?@\\^~".toList.map Char.toNat
  [.maximalToken "PlWord" rest [], .maximalToken "PlVariableName" rest [],
   .maximalToken "PlGraphicWord" graphics [], .maximalToken "PlNumber" rest [],
   .maximalToken "PlLayout" [9, 10, 11, 12, 13, 32] ["%","/*"]] ++
  (if profile.dialect == .swi then [
    .maximalToken "PlOpenHexEscape" ("0123456789abcdefABCDEF".toList.map Char.toNat) ["\\"],
    .maximalToken "PlOpenOctEscape" ("01234567".toList.map Char.toNat) ["\\"]] else []) ++
  (profile.operators.zipIdx.map fun (op, index) =>
    .maximalToken ("PlOperator" ++ toString index)
      (if op.name.toList.all Char.isAlphanum then rest else graphics) [])

theorem common_rows_retained (profile : Profile) : commonRows ⊆ (grammar profile).terms := by
  intro r present
  exact List.mem_append_left _ (List.mem_append_left _ present)

end Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntax
