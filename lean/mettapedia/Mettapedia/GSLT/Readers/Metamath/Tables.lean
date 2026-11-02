import Mettapedia.GSLT.Readers.Metamath.Syntax
import Mettapedia.GSLT.Readers.SLR

/-!
# The Metamath reader's tables, computed from the `.module` ahead of time

`productions` lowers the rows of the `.module` grammar (token sorts become `tok` terminals),
`tables` is their SLR(1) automaton, and the printers below write the tables as MeTTa facts and as
a C header. The MeTTa vocabulary is prefixed (`rdr-shift`, `rdr-reduce`, ...): Prime evaluates a
function's arguments, and `reduce` is a Prime function, so table data must not share its names. Both generic engines (`rdr` in MeTTa, `reader.c` in C) read exactly this output; no
engine contains a Metamath rule.

Executable controls, checked when this file is checked: the automaton has no SLR conflict and no
token conflict (no token can be two terminals that ask for different actions in one state).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.Metamath.Tables

open Mettapedia.GSLT.Readers.SLR
open Mettapedia.GSLT.Readers.TokenProfile
open Mettapedia.GSLT.Readers.Metamath

def tokenSorts : List String := profile.classes.map (·.1)

def productions : List Prod := (SLR.productions tokenSorts profile.start grammar).getD []

def tables : Tables := build productions

/-- A fixed spelling is a token of a token sort. -/
def member (sort spelling : String) : Bool := profile.tokenHasSort sort (codes spelling)

/-- Two token sorts share a token (a single shared byte suffices). -/
def classesMeet (a b : String) : Bool :=
  match profile.classOf? a, profile.classOf? b with
  | some x, some y => x.members.any (y.members.contains ·)
  | _, _ => false

#guard productions.length == grammar.terms.length + 1
#guard tables.conflicts.isEmpty
#guard (tokenConflicts member classesMeet tables).isEmpty

/-! ## Printing the tables -/

def quote (text : String) : String :=
  "\"" ++ (text.toList.map fun c => if c == '"' then "\\\"" else if c == '\\' then "\\\\" else c.toString).foldl (· ++ ·) "" ++ "\""

def symMetta : Sym → String
  | .lit s => "(rdr-lit " ++ quote s ++ ")"
  | .tok c => "(rdr-tok " ++ c ++ ")"
  | .eof => "rdr-eof"
  | .nt n => "(rdr-nt " ++ n ++ ")"

def actionMetta : Action → String
  | .shift s => s!"(rdr-shift {s})"
  | .reduce p => s!"(rdr-reduce {p})"
  | .accept => "rdr-accept"

def natsMetta (ns : List Nat) : String := "(" ++ " ".intercalate (ns.map toString) ++ ")"


/-! The C header: terminals are numbered `0` (end of input), then the fixed spellings, then the
token sorts; phrase sorts are numbered separately. -/

def terminals : List Sym :=
  .eof :: ((tables.prods.flatMap (·.rhs)).filter (fun s => match s with
    | .lit _ => true | _ => false)).eraseDups ++ tokenSorts.map .tok

def phraseSorts : List String := (tables.prods.map (·.lhs)).eraseDups

def termIndex (s : Sym) : Nat := (terminals.findIdx? (· == s)).getD 0
def sortIndex (n : String) : Nat := (phraseSorts.findIdx? (· == n)).getD 0

/-- The tables as MeTTa equations over the language name `lang`. A Prime function's argument
reaches an equation's head but not a `match` or `transform` pattern, so lookups keyed by state,
terminal or sort are equations; the action and goto tables are total (`rdr-error`, `-1`). -/
def mettaText (lang : String) : String :=
  let header := s!"; Generated from MetamathSyntax.module by Mettapedia.GSLT.Readers.Metamath.Tables.\n" ++
    s!"; {tables.prods.length} productions, {tables.states.length} states, " ++
    s!"{tables.actions.length} actions, {tables.gotos.length} gotos. Do not edit.\n"
  let nState := tables.states.length
  let lexical :=
    [s!"(= (rdr:start {lang}) {profile.start})",
     s!"(= (rdr:separator {lang}) {natsMetta profile.separator.members})",
     s!"(= (rdr:admissible {lang}) {natsMetta profile.admissible.members})",
     s!"(= (rdr:comment {lang}) ({quote profile.commentOpen} {quote profile.commentClose}))",
     s!"(= (rdr:token-sorts {lang}) (" ++ " ".intercalate (tokenSorts.map fun c =>
        s!"({c} {termIndex (.tok c)})") ++ "))"]
  let spellings := terminals.filterMap fun t => match t with
    | .lit s => some s!"(= (rdr:spelling-terminal {lang} {quote s}) {termIndex t})"
    | _ => none
  let prods := (List.range tables.prods.length).map fun i =>
    let p := tables.prods.getD i default
    s!"(= (rdr:prod {lang} {i}) ({quote p.label} {p.lhs} {p.rhs.length} (" ++
      " ".intercalate (p.rhs.map symMetta) ++ ")))"
  let acts := (List.range nState).flatMap fun s => terminals.map fun t =>
    let act := match tables.actions.find? (fun (s', a, _) => s' == s && a == t) with
      | some (_, _, a) => actionMetta a
      | none => "rdr-error"
    s!"(= (rdr:action {lang} {s} {termIndex t}) {act})"
  let gotos := (List.range nState).flatMap fun s => phraseSorts.map fun n =>
    let g := match tables.gotos.find? (fun (s', n', _) => s' == s && n' == n) with
      | some (_, _, t) => toString t
      | none => "-1"
    s!"(= (rdr:goto {lang} {s} {n}) {g})"
  let classes := profile.classes.flatMap fun (sort, set) =>
    (List.range 256).map fun b =>
      s!"(= (rdr:class-byte {lang} {sort} {b}) {if set.members.contains b then "True" else "False"})"
  header ++ "\n".intercalate (lexical ++ spellings ++ prods ++ acts ++ gotos ++ classes) ++ "\n"

def cString (text : String) : String := quote text

def cHeader (prefix_ : String) : String :=
  let p := prefix_
  let nTerm := terminals.length
  let nSort := phraseSorts.length
  let nState := tables.states.length
  let actionCell (s : Nat) (t : Sym) : String :=
    match (tables.actions.find? fun (s', a, _) => s' == s && a == t) with
    | some (_, _, .shift n) => s!"{n + 1}"
    | some (_, _, .reduce q) => s!"-{q + 1}"
    | some (_, _, .accept) => "ACCEPT"
    | none => "0"
  let gotoCell (s : Nat) (n : String) : String :=
    match (tables.gotos.find? fun (s', n', _) => s' == s && n' == n) with
    | some (_, _, t) => s!"{t}"
    | none => "-1"
  let classRow (sort : String) : String :=
    let members := ((profile.classOf? sort).map ByteSet.members).getD []
    "{" ++ ", ".intercalate ((List.range 256).map fun b => if members.contains b then "1" else "0") ++ "}"
  let byteRow (set : ByteSet) : String :=
    "{" ++ ", ".intercalate ((List.range 256).map fun b => if set.members.contains b then "1" else "0") ++ "}"
  "/* Generated from MetamathSyntax.module by Mettapedia.GSLT.Readers.Metamath.Tables. Do not edit. */\n" ++
  s!"#define {p}_TERMINALS {nTerm}\n#define {p}_SORTS {nSort}\n#define {p}_STATES {nState}\n" ++
  s!"#define {p}_PRODS {tables.prods.length}\n#define {p}_TOKEN_SORTS {tokenSorts.length}\n" ++
  s!"#define {p}_FIRST_TOKEN_SORT {nTerm - tokenSorts.length}\n" ++
  s!"#define {p}_START_SORT {sortIndex profile.start}\n" ++
  s!"static const char *{p}_terminal_spelling[] = \{" ++ ", ".intercalate (terminals.map fun
    | .lit s => cString s | .tok c => cString c | _ => "\"$eof\"") ++ "};\n" ++
  s!"static const int {p}_terminal_is_sort[] = \{" ++ ", ".intercalate (terminals.map fun
    | .tok _ => "1" | _ => "0") ++ "};\n" ++
  s!"static const char *{p}_sort_name[] = \{" ++ ", ".intercalate (phraseSorts.map cString) ++ "};\n" ++
  s!"static const char *{p}_prod_label[] = \{" ++ ", ".intercalate (tables.prods.map fun q => cString q.label) ++ "};\n" ++
  s!"static const int {p}_prod_lhs[] = \{" ++ ", ".intercalate (tables.prods.map fun q => toString (sortIndex q.lhs)) ++ "};\n" ++
  s!"static const int {p}_prod_len[] = \{" ++ ", ".intercalate (tables.prods.map fun q => toString q.rhs.length) ++ "};\n" ++
  s!"static const int {p}_prod_rhs[][2 * 12] = \{" ++ ", ".intercalate (tables.prods.map fun q =>
    if q.rhs.isEmpty then "{0}" else
    "{" ++ ", ".intercalate (q.rhs.map fun s => match s with
      | .nt n => s!"1, {sortIndex n}" | t => s!"0, {termIndex t}") ++ "}") ++ "};\n" ++
  s!"#define {p}_ACCEPT 1000000\n" ++
  s!"static const int {p}_action[{nState}][{nTerm}] = \{\n" ++ ",\n".intercalate ((List.range nState).map fun s =>
    "  {" ++ ", ".intercalate (terminals.map fun t => (actionCell s t).replace "ACCEPT" s!"{p}_ACCEPT") ++ "}") ++ "\n};\n" ++
  s!"static const int {p}_goto[{nState}][{nSort}] = \{\n" ++ ",\n".intercalate ((List.range nState).map fun s =>
    "  {" ++ ", ".intercalate (phraseSorts.map (gotoCell s)) ++ "}") ++ "\n};\n" ++
  s!"static const unsigned char {p}_class[{tokenSorts.length}][256] = \{\n" ++
    ",\n".intercalate (tokenSorts.map classRow) ++ "\n};\n" ++
  s!"static const unsigned char {p}_separator[256] = " ++ byteRow profile.separator ++ ";\n" ++
  s!"static const unsigned char {p}_admissible[256] = " ++ byteRow profile.admissible ++ ";\n" ++
  s!"static const char *{p}_comment_open = {cString profile.commentOpen};\n" ++
  s!"static const char *{p}_comment_close = {cString profile.commentClose};\n"

#guard (tables.prods.map (·.rhs.length)).all (· ≤ 12)

end Mettapedia.GSLT.Readers.Metamath.Tables
