import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.Readers.TokenProfileV2

/-!
# The rho calculus in CeTTa's mrho syntax, read from its `.module` presentation

`cetta --lang rhocalc --syntax mrho` reads a file of strict-core rho processes written as MeTTa
S-expressions, runs each one, and prints its residual in the same syntax.
`metta/gslt/module/readers/rho/MrhoSyntax.module` presents that syntax as three pieces (`Names`,
`Processes`, `Files`) joined over one shared `Sorts` value, plus the lexical layer (`Tokens`) as a
version-2 token profile and the binding structure (`Scopes`), both returned by a message. Each row
is one case of the reference's strict-core check (`rho_check_proc`, `rho_check_name`).

The `.module` file is read when this file is elaborated; Lake does not track it, so a change to it
needs a change here before a build sees it (version: second, a parallel composition's component list ends at its `)`).

Results:
* `grammar`: the composed grammar; `grammar_rows`, `grammar_types`: its size and sorts.
* `profile`: the decoded lexical layer; `profile_facts`: the six C-locale space bytes separate
  tokens, the two parentheses are tokens by themselves, `;` opens a line comment, and the one
  token sort is the variable.
* `token_controls`: `$x`, `$x_rho1` and `$a$b` are variables; `$` alone, `x`, `rho:nil`, and a
  token holding `;` or `"` are not.
* `tokenize_controls`: a process line is cut into its tokens; a comment at the start of a token
  runs to the end of the line; a tab separates; a byte outside printable ASCII is a fault, also
  inside a comment; a `;` inside a token does not start a comment.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.Readers.Rho

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet codes)
open Mettapedia.GSLT.Readers.TokenProfileV2

#module_file "../../../../../../metta/gslt/module/readers/rho/MrhoSyntax.module"

/-- The grammar the `.module` elaborates to. -/
def grammar? : Option LanguageDef := MrhoSyntax.language.toOption

def grammar : LanguageDef := grammar?.get (by decide +kernel)

theorem grammar_elaborated : grammar? = some grammar := (Option.some_get _).symm

theorem grammar_rows : grammar.terms.length = 12 := by decide +kernel

theorem grammar_types : grammar.types.length = 6 := by decide +kernel

/-- The rows, by label and sort, in the order of the `.module`. -/
theorem grammar_labels :
    grammar.terms.map (fun r => (r.label, r.category)) =
      [("name_quote", "rho_name"), ("name_var", "rho_name"), ("proc_nil", "rho_proc"),
        ("proc_par", "rho_proc"), ("proc_send", "rho_proc"), ("proc_recv", "rho_proc"),
        ("proc_drop", "rho_proc"), ("procs_end", "rho_procs"), ("procs_more", "rho_procs"),
        ("item_proc", "rho_item"), ("file_empty", "mrho_file"), ("file_more", "mrho_file")] := by
  decide +kernel

/-! ## The lexical layer -/

/-- The reply a theory of the module gives to its one message, if it has exactly one. -/
def reply? (part message : String) : Option Pattern := do
  let (_, fragment) ← (ModuleSource.applyTheory MrhoSyntax.library MrhoSyntax.module [part] []).toOption
  match fragment.entries.filterMap (fun entry => match entry.body with
      | ModuleSource.Decl.rewrite rule =>
          if rule.left == .apply message [] then some rule.right else none
      | _ => none) with
  | [reply] => some reply
  | _ => none

/-- The reply of the `ReturnTokenProfile` message, decoded as a version-2 profile. -/
def profile? : Option Profile := reply? "Tokens" "GetTokenProfile" >>= TokenProfileV2.profile?

def profile : Profile := profile?.get (by decide +kernel)

theorem profile_facts :
    profile.start = "mrho_file" ∧ profile.separator.members = [32, 10, 9, 11, 12, 13] ∧
      profile.delimiters.members = [40, 41] ∧ profile.lineComment = some ";" ∧
      profile.bracketComment = none ∧ profile.quote = none ∧
      profile.classes.map (·.sort) = ["var_tok"] := by
  decide +kernel

/-- A variable is `$` and at least one printable byte other than `"`, `(`, `)` and `;`; a keyword
of the grammar is no variable (it is a fixed spelling only). -/
theorem token_controls :
    profile.tokenHasSort "var_tok" (codes "$x") = true ∧
      profile.tokenHasSort "var_tok" (codes "$x_rho1") = true ∧
      profile.tokenHasSort "var_tok" (codes "$a$b") = true ∧
      profile.tokenHasSort "var_tok" (codes "$") = false ∧
      profile.tokenHasSort "var_tok" (codes "x") = false ∧
      profile.tokenHasSort "var_tok" (codes "rho:nil") = false ∧
      profile.tokenHasSort "var_tok" (codes "$x;c") = false ∧
      profile.tokenHasSort "var_tok" (codes "$x\"") = false := by
  decide +kernel

/-- A process line is cut into its tokens; `;` at the start of a token begins a comment to the end
of the line, also right after a parenthesis; a tab is a separator; a byte outside printable ASCII
is a fault even inside a comment (the reference reads any byte there: a known gap); a `;` inside a
token is part of the token, which then has no sort (the reference ends the token there). -/
theorem tokenize_controls :
    tokenize profile (codes "(rho:send $x rho:nil) ; c\n") =
        .ok [(0, codes "("), (1, codes "rho:send"), (10, codes "$x"), (13, codes "rho:nil"),
          (20, codes ")")] ∧
      tokenize profile (codes "(;c\nrho:nil)") = .ok [(0, codes "("), (4, codes "rho:nil"), (11, codes ")")] ∧
      tokenize profile (codes "(rho:drop\t$x)") =
        .ok [(0, codes "("), (1, codes "rho:drop"), (10, codes "$x"), (12, codes ")")] ∧
      tokenize profile ((codes "; ") ++ [194, 167] ++ codes "\nrho:nil") =
        .error (.inadmissibleByte 2 194) ∧
      tokenize profile (codes "$x;c") = .ok [(0, codes "$x;c")] := by
  decide +kernel

end Mettapedia.GSLT.Readers.Rho
