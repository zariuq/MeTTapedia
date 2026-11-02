import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.Readers.TokenProfileV2

/-!
# MM0's proof file format, read from its `.module` presentation

`metta/gslt/module/readers/mm0/MMUSyntax.module` presents the `.mmu` format as five pieces
(`Exprs`, `Binders`, `Proofs`, `Statements`, `Files`) joined over one shared `Sorts` value, plus
the lexical layer (`Tokens`) as a version-2 token profile returned by a message.

Results:
* `grammar`: the composed grammar; `grammar_rows`, `grammar_types`: its size and sorts.
* `profile`: the decoded lexical layer, with its facts: only space and newline separate tokens
  (`profile_separator`), `(` and `)` are tokens by themselves (`profile_delimiters`), `--` opens a
  line comment (`profile_line_comment`), and identifiers are MM0's
  `[a-zA-Z_][a-zA-Z0-9_]*` without `_` alone (`profile_identifier_controls`).
* `tokenize_controls`: the lexical faults the MM0 test suite expects (a tab, a carriage return,
  a non-ASCII byte) are faults here, and a comment inside a statement is trivia.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.Readers.MM0

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet codes)
open Mettapedia.GSLT.Readers.TokenProfileV2

#module_file "../../../../../../metta/gslt/module/readers/mm0/MMUSyntax.module"

/-- The grammar the `.module` elaborates to. -/
def grammar? : Option LanguageDef := MMUSyntax.language.toOption

def grammar : LanguageDef := grammar?.get (by decide +kernel)

theorem grammar_elaborated : grammar? = some grammar := (Option.some_get _).symm

theorem grammar_rows : grammar.terms.length = 48 := by decide +kernel

theorem grammar_types : grammar.types.length = 19 := by decide +kernel

/-! ## The lexical layer -/

def tokensFragment : Except ModuleSource.Error (String × ModuleSource.Value) :=
  ModuleSource.applyTheory MMUSyntax.library MMUSyntax.module ["Tokens"] []

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

theorem profile_start : profile.start = "mmu_file" := by decide +kernel

theorem profile_separator : profile.separator.members = [32, 10] := by decide +kernel

theorem profile_delimiters : profile.delimiters.members = [40, 41] := by decide +kernel

theorem profile_line_comment : profile.lineComment = some "--" ∧ profile.bracketComment = none := by
  decide +kernel

/-- MM0 identifiers: a letter or `_`, then letters, digits and `_`; `_` alone is not one. -/
theorem profile_identifier_controls :
    profile.tokenHasSort "id_tok" (codes "ax_mp") = true ∧
      profile.tokenHasSort "id_tok" (codes "_id3") = true ∧
      profile.tokenHasSort "id_tok" (codes "Id2_") = true ∧
      profile.tokenHasSort "id_tok" (codes "0") = false ∧
      profile.tokenHasSort "id_tok" (codes "sot-") = false ∧
      profile.tokenHasSort "id_tok" (codes "_") = false := by
  decide +kernel

/-- The lexical cases of MM0's test suite: a comment inside a statement is trivia; a tab, a
carriage return and a non-ASCII byte are faults. -/
theorem tokenize_controls :
    tokenize profile (codes "(sort \n-- comment inside a directive\ns)") =
        .ok [(0, codes "("), (1, codes "sort"), (37, codes "s"), (38, codes ")")] ∧
      tokenize profile (codes "(sort s\t)") = .error (.inadmissibleByte 7 9) ∧
      tokenize profile (codes "(sort s\r)") = .error (.inadmissibleByte 7 13) ∧
      tokenize profile ((codes "(sort ") ++ [195, 159] ++ codes ")") =
        .error (.inadmissibleByte 6 195) := by
  decide +kernel

end Mettapedia.GSLT.Readers.MM0
