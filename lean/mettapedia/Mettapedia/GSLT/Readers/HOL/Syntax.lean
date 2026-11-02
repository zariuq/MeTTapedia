import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.Readers.TokenProfileV2

/-!
# HOL Light's ProofTrace record, read from its `.module` presentation

`metta/gslt/module/readers/hol/ProofTraceSyntax.module` presents the three files HOL Light's
ProofTrace dumper writes (proof records, theorem records, name records) as six pieces (`Types`,
`Terms`, `Texts`, `Steps`, `Records`, `Files`) joined over one shared `Sorts` value, plus the
lexical layer (`Tokens`) as a version-2 token profile returned by a message.

Results:
* `grammar`: the composed grammar; `grammar_rows`, `grammar_types`: its size and sorts.
* `profile`: the decoded lexical layer, with its facts: only space and newline separate tokens
  (`profile_separator`); the JSON punctuation, the term brackets and the double quote are tokens by
  themselves (`profile_delimiters`); numbers, names and the quote are three token sorts
  (`profile_token_sorts`), a name being any printable run without a double quote, so a keyword or a
  single delimiter is also a name (`profile_name_controls`).
* `tokenize_controls`: a proof record is cut into its tokens (the quotes included); a tab and a
  non-ASCII byte are faults.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.Readers.HOL

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.GSLT.Readers.TokenProfile (ByteSet codes)
open Mettapedia.GSLT.Readers.TokenProfileV2

#module_file "../../../../../../metta/gslt/module/readers/hol/ProofTraceSyntax.module"

/-- The grammar the `.module` elaborates to. -/
def grammar? : Option LanguageDef := ProofTraceSyntax.language.toOption

def grammar : LanguageDef := grammar?.get (by decide +kernel)

theorem grammar_elaborated : grammar? = some grammar := (Option.some_get _).symm

theorem grammar_rows : grammar.terms.length = 43 := by decide +kernel

theorem grammar_types : grammar.types.length = 20 := by decide +kernel

/-! ## The lexical layer -/

def tokensFragment : Except ModuleSource.Error (String × ModuleSource.Value) :=
  ModuleSource.applyTheory ProofTraceSyntax.library ProofTraceSyntax.module ["Tokens"] []

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

theorem profile_start : profile.start = "trace_file" := by decide +kernel

theorem profile_separator : profile.separator.members = [32, 10] := by decide +kernel

/-- `{ } [ ] ( ) , : "` are tokens by themselves. -/
theorem profile_delimiters :
    profile.delimiters.members = [123, 125, 91, 93, 40, 41, 44, 58, 34] := by decide +kernel

theorem profile_no_comments : profile.lineComment = none ∧ profile.bracketComment = none := by
  decide +kernel

theorem profile_token_sorts :
    profile.classes.map (·.sort) = ["num_tok", "name_tok", "quote_tok"] := by decide +kernel

/-- Names: HOL Light's constant and variable names as its printer writes them (`String.escaped`).
A keyword of the grammar and a single delimiter are names too; a double quote is not. -/
theorem profile_name_controls :
    profile.tokenHasSort "name_tok" (codes "/\\\\") = true ∧
      profile.tokenHasSort "name_tok" (codes "==>") = true ∧
      profile.tokenHasSort "name_tok" (codes "_2064") = true ∧
      profile.tokenHasSort "name_tok" (codes "REFL") = true ∧
      profile.tokenHasSort "name_tok" (codes ",") = true ∧
      profile.tokenHasSort "name_tok" (codes "\"") = false ∧
      profile.tokenHasSort "num_tok" (codes "4071") = true ∧
      profile.tokenHasSort "num_tok" (codes "x1") = false ∧
      profile.tokenHasSort "quote_tok" (codes "\"") = true ∧
      profile.tokenHasSort "quote_tok" (codes "\"\"") = false := by
  decide +kernel

/-- A proof record is cut into its tokens, the JSON quotes included; a tab and a non-ASCII byte
are faults. -/
theorem tokenize_controls :
    tokenize profile (codes "{\"id\": 4, \"pr\": [\"MK_COMB\", 3, 0]}") =
        .ok [(0, codes "{"), (1, codes "\""), (2, codes "id"), (4, codes "\""), (5, codes ":"),
          (7, codes "4"), (8, codes ","), (10, codes "\""), (11, codes "pr"), (13, codes "\""),
          (14, codes ":"), (16, codes "["), (17, codes "\""), (18, codes "MK_COMB"),
          (25, codes "\""), (26, codes ","), (28, codes "3"), (29, codes ","), (31, codes "0"),
          (32, codes "]"), (33, codes "}")] ∧
      tokenize profile (codes "{\"id\":\t4}") = .error (.inadmissibleByte 6 9) ∧
      tokenize profile ((codes "{\"id\": ") ++ [195, 159] ++ codes "}") =
        .error (.inadmissibleByte 7 195) := by
  decide +kernel

end Mettapedia.GSLT.Readers.HOL
