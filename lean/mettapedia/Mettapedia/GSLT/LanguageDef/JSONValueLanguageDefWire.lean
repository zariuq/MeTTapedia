import Mettapedia.GSLT.LanguageDef.JSONParserPackNTT
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Occurrence-preserving JSON value wire projection

The JSON value carrier used by external realizations is rendered from the
authored Lean `LanguageDef`.  Object-member occurrence identity and source
spans are therefore part of the supplied target presentation rather than an
independently maintained C convention.
-/

namespace Mettapedia.GSLT.LanguageDef.JSONValueLanguageDefWire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.JSONParserPackNTT

abbrev renderLanguage? :=
  Mettapedia.GSLT.LanguageDef.CanonicalWire.renderLanguage?

/-- The occurrence-preserving JSON target lies in the canonical first-order
wire profile consumed by external LanguageDef transformers. -/
theorem wire_isSome :
    (renderLanguage? jsonValue).isSome := by
  decide +kernel

/-- Canonical generated wire text for the occurrence-preserving JSON target. -/
def wire : String :=
  (renderLanguage? jsonValue).getD ""

theorem wire_nonempty : wire != "" := by
  decide +kernel

private def memberWithoutSpan : GrammarRule := {
  label := "JsonMemberV1"
  category := "Member"
  params := [
    .simple "occurrence" (.base "OccurrenceId"),
    .simple "key" (.base "Value"),
    .simple "value" (.base "Value")]
  syntaxPattern := [.terminal "JsonMemberV1"]
  evalPolicy? := none
}

/-- Negative control: removing the member source span is a semantic target
mutation rather than a presentation-only rename. -/
def jsonValueWithoutMemberSpan : LanguageDef := {
  jsonValue with
  terms := jsonValue.terms.set 6 memberWithoutSpan
}

private def memberParameterCount? (language : LanguageDef) : Option Nat :=
  (language.terms.drop 6).head?.map fun rule => rule.params.length

theorem removing_member_span_changes_target_shape :
    memberParameterCount? jsonValueWithoutMemberSpan = some 3 ∧
      memberParameterCount? jsonValue = some 4 := by
  decide

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_isSome
#print axioms wire_nonempty
#print axioms removing_member_span_changes_target_shape

end Mettapedia.GSLT.LanguageDef.JSONValueLanguageDefWire
