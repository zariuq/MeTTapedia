import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence

/-! An authored source grammar and its explicit scalar-profile port. The
grammar, profile, source selection and binding interpretation remain distinct.
This reader shares the same module interfaces across source languages. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax

def profileRequest : Pattern := .apply "GetLexicalProfile" []

def replyAt? (library : List (String × ModuleSource.Module))
    (module : ModuleSource.Module) (theory port : String) (request : Pattern) :
    Option (ModuleSource.Item × Pattern) := do
  let (_, fragment) ← (ModuleSource.applyTheory library module [theory] []).toOption
  match fragment.entries.filter (fun entry => entry.label == (.rewrite, port)) with
  | [entry] =>
      match entry.body with
      | .rewrite rule =>
          if rule.left == request && rule.premises.isEmpty && rule.bindings.isNone then
            some (entry, rule.right)
          else none
      | _ => none
  | _ => none

def lexicalReplyAt? (library : List (String × ModuleSource.Module))
    (module : ModuleSource.Module) (port : String) (request : Pattern) :
    Option (ModuleSource.Item × Parsing.ParserProfileSemantics.ParserProfileLayer) := do
  let (entry, data) ← replyAt? library module "LexicalProfile" port request
  pure (entry, ← Portable.readLexicalData? data)

inductive FamilyFilter where
  | rejectWords (sort : String) (words : List String)
  | maximalToken (sort : String) (continuations : List Nat) (openers : List String)
  | maximalExcept (sort : String) (excluded : List Nat) (openers : List String)
  deriving Repr, DecidableEq

def string? : Pattern → Option String
  | .apply text [] => some text
  | _ => none

def list? {α : Type} (element : Pattern → Option α) : Pattern → Option (List α)
  | .apply "LNil" [] => some []
  | .apply "LCons" [head, tail] => do pure ((← element head) :: (← list? element tail))
  | _ => none

def familyFilter? : Pattern → Option FamilyFilter
  | .apply "RejectWords" [sort, words] => do
      pure (.rejectWords (← string? sort) (← list? string? words))
  | .apply "MaximalToken" [sort, points, openers] => do
      pure (.maximalToken (← string? sort)
        (← list? (fun point => (string? point).bind String.toNat?) points)
        (← list? string? openers))
  | .apply "MaximalExcept" [sort, points, openers] => do
      pure (.maximalExcept (← string? sort)
        (← list? (fun point => (string? point).bind String.toNat?) points)
        (← list? string? openers))
  | _ => none

def selection? (library : List (String × ModuleSource.Module))
    (module : ModuleSource.Module) : Option (List FamilyFilter) := do
  let (_, data) ← replyAt? library module "SourceSelection" "ReturnSourceSelection"
    (.apply "GetSourceSelection" [])
  match data with
  | .apply "SourceSelectionV1" [filters] => list? familyFilter? filters
  | _ => none

/-- A local selection examines a category's exact source span and the remaining
scalars. It does not choose between unrelated derivations or erase the forest. -/
def FamilyFilter.allows (sort : String) (word suffix : List Nat) : FamilyFilter → Bool
  | .rejectWords target words => sort != target ||
      !(words.any fun text => text.toList.map Char.toNat == word)
  | .maximalToken target continuations openers => sort != target ||
      (!(suffix.head?.any continuations.contains) &&
        !(openers.any fun text => (text.toList.map Char.toNat).isPrefixOf suffix))
  | .maximalExcept target excluded openers => sort != target ||
      (!(suffix.head?.any fun point => !excluded.contains point) &&
        !(openers.any fun text => (text.toList.map Char.toNat).isPrefixOf suffix))

def description? (library : List (String × ModuleSource.Module))
    (module : ModuleSource.Module) : Option Portable.SyntaxDescription := do
  let grammar ← (ModuleSource.elaborate library module).toOption
  let (_, profile) ← lexicalReplyAt? library module "ReturnLexicalProfile" profileRequest
  pure ⟨grammar, profile⟩

/-- Text transport recovers the complete grammar and lexical profile. It does
not assert a source-language parsing or execution correspondence. -/
theorem optional_text_roundtrip (description : Option Portable.SyntaxDescription) :
    (description.map Portable.renderSyntax).bind Portable.readSyntax? = description := by
  cases description with
  | none => rfl
  | some value => simpa only [Option.map_some, Option.bind_some] using
      Portable.readSyntax_renderSyntax value

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntax
