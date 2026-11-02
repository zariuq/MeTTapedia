import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.Readers.TokenProfileV2

/-!
# Megalodon's own record of a checked document, read from its `.module` presentation

`megalodon -sexprinfo` prints, for every declaration it admits, one S-expression line, and for each
theorem the proof term its kernel double-checked, with the knowns the check used and the
definitions it unfolded. `metta/gslt/module/readers/megalodon/SexprInfoSyntax.module` presents that
record as six pieces (`Numerals`, `SimpleTypes`, `MgTerms`, `MgProofs`, `Items`, `Files`) joined over
one shared `Sorts` value, plus the lexical layer (`Tokens`) as a version-2 token profile returned by a
message. Each row is one case of Megalodon's printers (`tp_to_sexpr`, `tm_to_sexpr`, `pf_to_sexpr`,
and the `-sexprinfo` lines of `megalodon.ml`).

The `.module` file is read when this file is elaborated; Lake does not track it, so a change to it
needs a change here before a build sees it (version: numerals as OCaml's `string_of_int` prints them).

Results:
* `grammar`: the composed grammar; `grammar_rows`, `grammar_types`: its size and sorts.
* `profile`: the decoded lexical layer; `profile_facts`: space and newline separate tokens, the two
  parentheses are tokens by themselves; `0`, a nonzero digit followed by digits, and a double-quoted
  string are the three token sorts.
* `token_controls`: `0` and `205` are numbers, `007` and `-1` are not; a string keeps its quotes and
  a space inside it; an unclosed string and a keyword are no strings.
* `tokenize_controls`: a record line is cut into its tokens; a tab and a non-ASCII byte are faults.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.Readers.Megalodon

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet codes)
open Mettapedia.GSLT.Readers.TokenProfileV2

#module_file "../../../../../../metta/gslt/module/readers/megalodon/SexprInfoSyntax.module"

/-- The grammar the `.module` elaborates to. -/
def grammar? : Option LanguageDef := SexprInfoSyntax.language.toOption

def grammar : LanguageDef := grammar?.get (by decide +kernel)

theorem grammar_elaborated : grammar? = some grammar := (Option.some_get _).symm

theorem grammar_rows : grammar.terms.length = 35 := by decide +kernel

theorem grammar_types : grammar.types.length = 11 := by decide +kernel

/-! ## The lexical layer -/

def tokensFragment : Except ModuleSource.Error (String × ModuleSource.Value) :=
  ModuleSource.applyTheory SexprInfoSyntax.library SexprInfoSyntax.module ["Tokens"] []

/-- The reply of the `ReturnTokenProfile` message, decoded as a version-2 profile. -/
def profile? : Option Profile := do
  let (_, fragment) ← tokensFragment.toOption
  match fragment.entries.filterMap (fun entry => match entry.body with
      | ModuleSource.Decl.rewrite rule =>
          if rule.left == .apply "GetTokenProfile" [] then some rule.right else none
      | _ => none) with
  | [reply] => TokenProfileV2.profile? reply
  | _ => none

def profile : Profile := profile?.get (by decide +kernel)

theorem profile_facts :
    profile.start = "sexpr_file" ∧ profile.separator.members = [32, 10] ∧
      profile.delimiters.members = [40, 41] ∧ profile.lineComment = none ∧
      profile.bracketComment = none ∧ profile.quote = some (34, 34) ∧
      profile.classes.map (·.sort) = ["zero_tok", "pos_tok", "str_tok"] := by
  decide +kernel

/-- Numbers are what OCaml's `string_of_int` prints for a natural number; a string is a run from a
double quote to the next one, both quotes included. A keyword of the grammar is neither (it is a
fixed spelling only). -/
theorem token_controls :
    profile.tokenHasSort "zero_tok" (codes "0") = true ∧
      profile.tokenHasSort "pos_tok" (codes "205") = true ∧
      profile.tokenHasSort "pos_tok" (codes "007") = false ∧
      profile.tokenHasSort "zero_tok" (codes "00") = false ∧
      profile.tokenHasSort "pos_tok" (codes "-1") = false ∧
      profile.tokenHasSort "str_tok" (codes "\"In\"") = true ∧
      profile.tokenHasSort "str_tok" (codes "\"a b\"") = true ∧
      profile.tokenHasSort "str_tok" (codes "\"") = false ∧
      profile.tokenHasSort "str_tok" (codes "\"ab") = false ∧
      profile.tokenHasSort "str_tok" (codes "PRIM") = false ∧
      profile.tokenHasSort "pos_tok" (codes "PRIM") = false := by
  decide +kernel

/-- A record line is cut into its tokens: parentheses alone, a string with both its quotes (a space
inside it kept), numbers; a tab and a non-ASCII byte are faults. -/
theorem tokenize_controls :
    tokenize profile (codes "(PRIM 1 \"In\" \"7a b\" (SET) 38)") =
        .ok [(0, codes "("), (1, codes "PRIM"), (6, codes "1"), (8, codes "\"In\""),
          (13, codes "\"7a b\""), (20, codes "("), (21, codes "SET"), (24, codes ")"),
          (26, codes "38"), (28, codes ")")] ∧
      tokenize profile (codes "(DB\t0)") = .error (.inadmissibleByte 3 9) ∧
      tokenize profile ((codes "(TMH \"") ++ [195, 159] ++ codes "\")") =
        .error (.inadmissibleByte 6 195) := by
  decide +kernel

end Mettapedia.GSLT.Readers.Megalodon
