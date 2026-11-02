import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.Readers.TokenProfileV2

/-!
# MM0's specification format, read from its `.module` presentation

`metta/gslt/module/readers/mm0/MM0Syntax.module` presents the outer grammar of `.mm0` files
(mm0.md, "Grammar for the `.mm0` file format") as five pieces (`Types`, `Binders`, `Notations`,
`Statements`, `Files`) joined over one shared `Sorts` value, and the lexical layer (`Tokens`) as a
version-2 token profile with quoted math strings. A def's type is an arrow type, as a term's is.

The `.module` file is read when this file is elaborated; Lake does not track it, so a change to it
needs a change here (this note's wording, if nothing else) before a build sees it.

Results:
* `grammar`: the composed grammar; `grammar_rows`, `grammar_types`: its size and sorts.
* `profile`: the decoded lexical layer; `profile_facts`: separators, the ten one-byte symbols,
  the line comment, and math strings quoted by `$`.
* `token_controls`: MM0's lexical rules on the cases of its test suite: identifiers
  (`[a-zA-Z_][a-zA-Z0-9_]*`, not `_` alone), numbers (`0 | [1-9][0-9]*`), a math string with a
  comment opener inside it; a tab is a fault.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.Readers.MM0.Spec

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet codes)
open Mettapedia.GSLT.Readers.TokenProfileV2

#module_file "../../../../../../metta/gslt/module/readers/mm0/MM0Syntax.module"

/-- The grammar the `.module` elaborates to. -/
def grammar? : Option LanguageDef := MM0Syntax.language.toOption

def grammar : LanguageDef := grammar?.get (by decide +kernel)

theorem grammar_elaborated : grammar? = some grammar := (Option.some_get _).symm

theorem grammar_rows : grammar.terms.length = 66 := by decide +kernel

theorem grammar_types : grammar.types.length = 28 := by decide +kernel

def tokensFragment : Except ModuleSource.Error (String × ModuleSource.Value) :=
  ModuleSource.applyTheory MM0Syntax.library MM0Syntax.module ["Tokens"] []

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
    profile.start = "mm0_file" ∧ profile.separator.members = [32, 10] ∧
      profile.delimiters.members = [42, 46, 58, 59, 40, 41, 62, 123, 125, 61] ∧
      profile.lineComment = some "--" ∧ profile.quote = some (36, 36) ∧
      profile.classes.map (·.sort) = ["id_tok", "num_tok", "math_tok"] := by
  decide +kernel

/-- MM0's lexical rules on the cases of its test suite. -/
theorem token_controls :
    profile.tokenHasSort "id_tok" (codes "ax_1") = true ∧
      profile.tokenHasSort "id_tok" (codes "_") = false ∧
      profile.tokenHasSort "id_tok" (codes "0") = false ∧
      profile.tokenHasSort "num_tok" (codes "2046") = true ∧
      profile.tokenHasSort "num_tok" (codes "01") = false ∧
      tokenize profile (codes "axiom a: $ x -- y $;") =
        .ok [(0, codes "axiom"), (6, codes "a"), (7, codes ":"), (9, codes "$ x -- y $"), (19, codes ";")] ∧
      tokenize profile (codes "sort s\t;") = .error (.inadmissibleByte 6 9) := by
  decide +kernel

end Mettapedia.GSLT.Readers.MM0.Spec
