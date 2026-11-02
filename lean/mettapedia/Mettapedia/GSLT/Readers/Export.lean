import Mettapedia.GSLT.Readers.SLR
import Mettapedia.GSLT.Readers.TokenProfileV2

/-!
# A reader's tables, for any `.module` grammar with a version-2 token profile

A `Spec` is a grammar and its lexical layer. `productions` lowers the grammar's rows (token sorts
become `tok` terminals), `tables` is their SLR(1) automaton, and the printers write the tables as
MeTTa equations and as a C header that the generic engines (`rdr` in MeTTa, `reader.c` in C)
read; no engine contains a rule of any language.

The lexical tables are those of `TokenProfileV2`: separator, admissible and delimiter bytes, the
line-comment opener, optional comment brackets, and for every token sort its first bytes, its
rest bytes and its excepted spellings. A version-1 profile is exported through
`TokenProfileV2.ofV1`, which gives the same tokens and token sorts (`tokenize_ofV1`,
`tokenHasSort_ofV1`).

`conflictFree` is the executable control each language checks: no SLR conflict, and no token that
two terminals could both read with different actions in one state.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.Export

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet codes)
open Mettapedia.GSLT.Readers.TokenProfileV2

structure Spec where
  name : String
  grammar : LanguageDef
  profile : Profile

namespace Spec

variable (s : Spec)

def tokenSorts : List String := s.profile.classes.map (·.sort)

def productions : List Prod := (SLR.productions s.tokenSorts s.profile.start s.grammar).getD []

def tables : Tables := build s.productions

/-- A fixed spelling is a token of a token sort. -/
def member (sort spelling : String) : Bool := s.profile.tokenHasSort sort (codes spelling)

/-- Two token sorts may share a token: their first bytes meet (a token's first byte is in the
first bytes of each of its sorts, so disjoint first bytes share no token). -/
def classesMeet (a b : String) : Bool :=
  match s.profile.classOf? a, s.profile.classOf? b with
  | some x, some y => x.first.members.any (y.first.members.contains ·)
  | _, _ => false

def conflictFree : Bool :=
  s.productions.length == s.grammar.terms.length + 1 && s.tables.conflicts.isEmpty &&
    (tokenConflicts s.member s.classesMeet s.tables).isEmpty &&
    (s.tables.prods.map (·.rhs.length)).all (· ≤ 24)

def terminals : List Sym :=
  .eof :: ((s.tables.prods.flatMap (·.rhs)).filter (fun x => match x with
    | .lit _ => true | _ => false)).eraseDups ++ s.tokenSorts.map .tok

def phraseSorts : List String := (s.tables.prods.map (·.lhs)).eraseDups

def termIndex (x : Sym) : Nat := (s.terminals.findIdx? (· == x)).getD 0
def sortIndex (n : String) : Nat := (s.phraseSorts.findIdx? (· == n)).getD 0

end Spec

def quote (text : String) : String :=
  "\"" ++ (text.toList.map fun c => if c == '"' then "\\\"" else if c == '\\' then "\\\\" else c.toString).foldl (· ++ ·) "" ++ "\""

def symMetta : Sym → String
  | .lit x => "(rdr-lit " ++ quote x ++ ")"
  | .tok c => "(rdr-tok " ++ c ++ ")"
  | .eof => "rdr-eof"
  | .nt n => "(rdr-nt " ++ n ++ ")"

def actionMetta : Action → String
  | .shift x => s!"(rdr-shift {x})"
  | .reduce p => s!"(rdr-reduce {p})"
  | .accept => "rdr-accept"

def natsMetta (ns : List Nat) : String := "(" ++ " ".intercalate (ns.map toString) ++ ")"

/-- The tables as MeTTa equations over the language name `lang`. A Prime function's argument
reaches an equation's head but not a `match` or `transform` pattern, so lookups keyed by state,
terminal or sort are equations; the action and goto tables are total (`rdr-error`, `-1`). -/
def mettaText (s : Spec) (lang : String) : String :=
  let t := s.tables
  let header := s!"; Generated from {s.name}.module by Mettapedia.GSLT.Readers.Export.\n" ++
    s!"; {t.prods.length} productions, {t.states.length} states, " ++
    s!"{t.actions.length} actions, {t.gotos.length} gotos. Do not edit.\n"
  let nState := t.states.length
  let p := s.profile
  let lexical :=
    [s!"(= (rdr:start {lang}) {p.start})",
     s!"(= (rdr:separator {lang}) {natsMetta p.separator.members})",
     s!"(= (rdr:admissible {lang}) {natsMetta p.admissible.members})",
     s!"(= (rdr:delimiters {lang}) {natsMetta p.delimiters.members})",
     s!"(= (rdr:line-comment {lang}) {quote (p.lineComment.getD "")})",
     s!"(= (rdr:comment {lang}) " ++ (match p.bracketComment with
        | some (o, c) => s!"({quote o} {quote c}))"
        | none => "rdr-none)"),
     s!"(= (rdr:quote {lang}) " ++ (match p.quote with
        | some (o, c) => s!"({o} {c}))"
        | none => "rdr-none)"),
     s!"(= (rdr:token-sorts {lang}) (" ++ " ".intercalate (s.tokenSorts.map fun c =>
        s!"({c} {s.termIndex (.tok c)})") ++ "))"]
  let spellings := s.terminals.filterMap fun x => match x with
    | .lit w => some s!"(= (rdr:spelling-terminal {lang} {quote w}) {s.termIndex x})"
    | _ => none
  let prods := (List.range t.prods.length).map fun i =>
    let q := t.prods.getD i default
    s!"(= (rdr:prod {lang} {i}) ({quote q.label} {q.lhs} {q.rhs.length} (" ++
      " ".intercalate (q.rhs.map symMetta) ++ ")))"
  let acts := (List.range nState).flatMap fun st => s.terminals.map fun x =>
    let act := match t.actions.find? (fun (s', a, _) => s' == st && a == x) with
      | some (_, _, a) => actionMetta a
      | none => "rdr-error"
    s!"(= (rdr:action {lang} {st} {s.termIndex x}) {act})"
  let gotos := (List.range nState).flatMap fun st => s.phraseSorts.map fun n =>
    let g := match t.gotos.find? (fun (s', n', _) => s' == st && n' == n) with
      | some (_, _, x) => toString x
      | none => "-1"
    s!"(= (rdr:goto {lang} {st} {n}) {g})"
  let classes := p.classes.flatMap fun c =>
    (List.range 256).flatMap fun b =>
      [s!"(= (rdr:first-byte {lang} {c.sort} {b}) {if c.first.members.contains b then "True" else "False"})",
       s!"(= (rdr:rest-byte {lang} {c.sort} {b}) {if c.rest.members.contains b then "True" else "False"})"]
  let excluded := p.classes.map fun c =>
    s!"(= (rdr:excluded {lang} {c.sort}) (" ++ " ".intercalate (c.excluded.map quote) ++ "))"
  let finals := p.classes.map fun c =>
    s!"(= (rdr:final-byte {lang} {c.sort}) {match c.final with | some f => toString f | none => "-1"})"
  header ++ "\n".intercalate (lexical ++ spellings ++ prods ++ acts ++ gotos ++ classes ++ excluded ++ finals) ++ "\n"

def byteRow (set : ByteSet) : String :=
  "{" ++ ", ".intercalate ((List.range 256).map fun b => if set.members.contains b then "1" else "0") ++ "}"

/-- The tables as a C header with prefix `p`. -/
def cHeader (s : Spec) (p : String) : String :=
  let t := s.tables
  let nTerm := s.terminals.length
  let nSort := s.phraseSorts.length
  let nState := t.states.length
  let prof := s.profile
  let actionCell (st : Nat) (x : Sym) : String :=
    match (t.actions.find? fun (s', a, _) => s' == st && a == x) with
    | some (_, _, .shift n) => s!"{n + 1}"
    | some (_, _, .reduce q) => s!"-{q + 1}"
    | some (_, _, .accept) => s!"{p}_ACCEPT"
    | none => "0"
  let gotoCell (st : Nat) (n : String) : String :=
    match (t.gotos.find? fun (s', n', _) => s' == st && n' == n) with
    | some (_, _, x) => s!"{x}"
    | none => "-1"
  let excludedPairs := prof.classes.zipIdx.flatMap fun (c, i) => c.excluded.map fun w => (i, w)
  s!"/* Generated from {s.name}.module by Mettapedia.GSLT.Readers.Export. Do not edit. */\n" ++
  s!"#define {p}_TERMINALS {nTerm}\n#define {p}_SORTS {nSort}\n#define {p}_STATES {nState}\n" ++
  s!"#define {p}_PRODS {t.prods.length}\n#define {p}_TOKEN_SORTS {s.tokenSorts.length}\n" ++
  s!"#define {p}_FIRST_TOKEN_SORT {nTerm - s.tokenSorts.length}\n" ++
  s!"#define {p}_START_SORT {s.sortIndex prof.start}\n" ++
  s!"static const char *{p}_terminal_spelling[] = \{" ++ ", ".intercalate (s.terminals.map fun
    | .lit w => quote w | .tok c => quote c | _ => "\"$eof\"") ++ "};\n" ++
  s!"static const int {p}_terminal_is_sort[] = \{" ++ ", ".intercalate (s.terminals.map fun
    | .tok _ => "1" | _ => "0") ++ "};\n" ++
  s!"static const char *{p}_sort_name[] = \{" ++ ", ".intercalate (s.phraseSorts.map quote) ++ "};\n" ++
  s!"static const char *{p}_prod_label[] = \{" ++ ", ".intercalate (t.prods.map fun q => quote q.label) ++ "};\n" ++
  s!"static const int {p}_prod_lhs[] = \{" ++ ", ".intercalate (t.prods.map fun q => toString (s.sortIndex q.lhs)) ++ "};\n" ++
  s!"static const int {p}_prod_len[] = \{" ++ ", ".intercalate (t.prods.map fun q => toString q.rhs.length) ++ "};\n" ++
  s!"static const int {p}_prod_rhs[][2 * 24] = \{" ++ ", ".intercalate (t.prods.map fun q =>
    if q.rhs.isEmpty then "{0}" else
    "{" ++ ", ".intercalate (q.rhs.map fun x => match x with
      | .nt n => s!"1, {s.sortIndex n}" | y => s!"0, {s.termIndex y}") ++ "}") ++ "};\n" ++
  s!"#define {p}_ACCEPT 1000000\n" ++
  s!"static const int {p}_action[{nState}][{nTerm}] = \{\n" ++ ",\n".intercalate ((List.range nState).map fun st =>
    "  {" ++ ", ".intercalate (s.terminals.map (actionCell st)) ++ "}") ++ "\n};\n" ++
  s!"static const int {p}_goto[{nState}][{nSort}] = \{\n" ++ ",\n".intercalate ((List.range nState).map fun st =>
    "  {" ++ ", ".intercalate (s.phraseSorts.map (gotoCell st)) ++ "}") ++ "\n};\n" ++
  s!"static const unsigned char {p}_class_first[{s.tokenSorts.length}][256] = \{\n" ++
    ",\n".intercalate (prof.classes.map fun c => byteRow c.first) ++ "\n};\n" ++
  s!"static const unsigned char {p}_class_rest[{s.tokenSorts.length}][256] = \{\n" ++
    ",\n".intercalate (prof.classes.map fun c => byteRow c.rest) ++ "\n};\n" ++
  s!"#define {p}_EXCLUDED {excludedPairs.length}\n" ++
  s!"static const int {p}_excluded_sort[] = \{" ++ ", ".intercalate (excludedPairs.map fun (i, _) => toString i) ++
    (if excludedPairs.isEmpty then "0" else "") ++ "};\n" ++
  s!"static const char *{p}_excluded_spelling[] = \{" ++ ", ".intercalate (excludedPairs.map fun (_, w) => quote w) ++
    (if excludedPairs.isEmpty then "\"\"" else "") ++ "};\n" ++
  s!"static const unsigned char {p}_separator[256] = " ++ byteRow prof.separator ++ ";\n" ++
  s!"static const unsigned char {p}_admissible[256] = " ++ byteRow prof.admissible ++ ";\n" ++
  s!"static const unsigned char {p}_delimiter[256] = " ++ byteRow prof.delimiters ++ ";\n" ++
  s!"static const char *{p}_line_comment = {quote (prof.lineComment.getD "")};\n" ++
  s!"static const char *{p}_comment_open = {quote ((prof.bracketComment.map (·.1)).getD "")};\n" ++
  s!"static const char *{p}_comment_close = {quote ((prof.bracketComment.map (·.2)).getD "")};\n" ++
  s!"static const int {p}_quote_open = {match prof.quote with | some (o, _) => toString o | none => "-1"};\n" ++
  s!"static const int {p}_quote_close = {match prof.quote with | some (_, c) => toString c | none => "-1"};\n" ++
  s!"static const int {p}_class_final[] = \{" ++ ", ".intercalate (prof.classes.map fun c =>
    match c.final with | some f => toString f | none => "-1") ++ "};\n"

end Mettapedia.GSLT.Readers.Export
