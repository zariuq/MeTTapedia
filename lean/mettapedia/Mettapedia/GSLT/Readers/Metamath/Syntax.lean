import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.Languages.Metamath.SourceGSLT
import Mettapedia.GSLT.Readers.RowShape
import Mettapedia.GSLT.Readers.TokenProfile

/-!
# Metamath's database syntax, read from its `.module` presentation

`metta/gslt/module/readers/metamath/MetamathSyntax.module` presents Metamath's database syntax
as three pieces (`Lists`, `Statements`, `Databases`) joined over one shared `Sorts` value, plus
the lexical layer (`Tokens`) as data returned by a message.

Results:
* `grammar_types`, `grammar_shapes`: the composed grammar has the sorts of the existing Lean root
  `SourceGSLT.sourceGrammar`, in order, and rows of the same shapes, in order. The one
  difference is a parameter name (`var`; the root writes `variable`, a word the Lean host
  of the module syntax reserves and that the other hosts cannot escape).
* `derives_iff_source`: the two grammars derive exactly the same trees from the same tokens, so
  every theorem about `sourceGrammar` (its compilation, its checked derivations, and its
  alignment with the verified reader of mm-lean4) holds for the `.module`.
* `profile_*`: the lexical layer of the `.module` is the authored lexical policy of the root:
  the same separator bytes, label bytes, math-symbol bytes, compressed-proof bytes and comment
  brackets.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.Readers.Metamath

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
open Mettapedia.GSLT.Readers.RowShape
open Mettapedia.GSLT.Readers.TokenProfile

#module_file "../../../../../../metta/gslt/module/readers/metamath/MetamathSyntax.module"

/-- The grammar the `.module` elaborates to. -/
def grammar? : Option LanguageDef := MetamathSyntax.language.toOption

def grammar : LanguageDef := grammar?.get (by decide +kernel)

theorem grammar_elaborated : grammar? = some grammar := (Option.some_get _).symm

private def source : LanguageDef := Mettapedia.Languages.Metamath.SourceGSLT.sourceGrammar

theorem grammar_types : grammar.types = source.types := by decide +kernel

theorem grammar_shapes : grammar.terms.map rowShape = source.terms.map rowShape := by
  decide +kernel

/-- The `.module` and the authored Lean root derive the same trees from the same tokens. -/
theorem derives_iff_source (sort : String) (toks : List String) (tree : Pattern) :
    Derives grammar sort toks tree ↔ Derives source sort toks tree :=
  derives_iff_of_shapes grammar_shapes sort toks tree

/-- Negative control: the rows are not literally equal (one parameter name differs), so the
shape theorem, not syntactic equality, carries the correspondence. -/
theorem grammar_terms_differ_only_by_names : grammar.terms ≠ source.terms := by decide +kernel

/-! ## The lexical layer -/

def tokensFragment : Except ModuleSource.Error (String × ModuleSource.Value) :=
  ModuleSource.applyTheory MetamathSyntax.library MetamathSyntax.module ["Tokens"] []

/-- The reply of the `ReturnTokenProfile` message, decoded. -/
def profile? : Option Profile := do
  let (_, fragment) ← tokensFragment.toOption
  match fragment.entries.filterMap (fun entry => match entry.body with
      | ModuleSource.Decl.rewrite rule =>
          if rule.left == .apply "GetTokenProfile" [] then some rule.right else none
      | _ => none) with
  | [reply] => TokenProfile.profile? reply
  | _ => none

def profile : Profile := profile?.get (by decide +kernel)

theorem profile_start : profile.start = "outer_database" := by decide +kernel

open Mettapedia.Languages.Metamath.SourceGSLT in
theorem profile_separator : profile.separator.members = whitespaceCodepoints := by decide +kernel

open Mettapedia.Languages.Metamath.SourceGSLT in
theorem profile_label : (profile.classOf? "label_tok").map ByteSet.members = some labelCodepoints := by
  decide +kernel

open Mettapedia.Languages.Metamath.SourceGSLT in
theorem profile_proof_label :
    (profile.classOf? "proof_label_tok").map ByteSet.members = some labelCodepoints := by
  decide +kernel

open Mettapedia.Languages.Metamath.SourceGSLT in
theorem profile_symbol :
    (profile.classOf? "symbol_tok").map ByteSet.members = some mathSymbolCodepoints := by
  decide +kernel

open Mettapedia.Languages.Metamath.SourceGSLT in
theorem profile_include_path :
    (profile.classOf? "include_path_tok").map ByteSet.members = some mathSymbolCodepoints := by
  decide +kernel

open Mettapedia.Languages.Metamath.SourceGSLT in
theorem profile_compressed :
    (profile.classOf? "compressed_word_tok").map ByteSet.members = some compressedCodepoints := by
  decide +kernel

open Mettapedia.Languages.Metamath.SourceGSLT in
theorem profile_comment :
    codes profile.commentOpen = commentOpenCodepoints ∧
      codes profile.commentClose = commentCloseCodepoints := by
  decide +kernel

/-- Every token sort of the grammar (a sort with no row) has exactly one byte set. -/
theorem profile_covers_token_sorts :
    ["label_tok", "symbol_tok", "proof_label_tok", "compressed_word_tok",
      "include_path_tok"].all (fun sort => (profile.classOf? sort).isSome) = true := by
  decide +kernel

end Mettapedia.GSLT.Readers.Metamath
