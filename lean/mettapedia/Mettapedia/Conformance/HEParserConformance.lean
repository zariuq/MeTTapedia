import Algorithms.MeTTa.Simple.Parser
import Mettapedia.Languages.MeTTa.HE.SyntaxSpec

/-!
# HE Parser Conformance

Concrete parser-conformance checks for the authoritative HE syntax profiles.

This file is intentionally a conformance bridge:
- syntax authority lives in `Mettapedia.Languages.MeTTa.HE.SyntaxSpec`
- actual parser behavior comes from `Algorithms.MeTTa.Simple.Parser`

The checks here are deliberately curated around the syntax points that matter
most for current HE compatibility and the newly declared canonical surface.

This module intentionally exposes **executable conformance fixtures**, not
kernel theorems. The parser computations here do not reduce far enough for
plain `decide`, and `native_decide` is not acceptable in this trust model.
So the honest artifact is a curated Bool-valued fixture pack that downstream
checks can run against the actual parser implementation.
-/

namespace Mettapedia.Conformance.HEParserConformance

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple.Parser
open Mettapedia.Languages.MeTTa.HE

private def sym (s : String) : Pattern := .apply s []
private def app (f : String) (args : List Pattern) : Pattern := .apply f args

private def parseLineOk? (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec)
    (line : String) (expected : Stmt) : Bool :=
  match parseLineWith spec line with
  | .ok stmt => decide (stmt = expected)
  | .error _ => false

private def parseProgramOk? (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec)
    (text : String) (expected : List (Nat × Stmt)) : Bool :=
  match parseProgramWith spec text with
  | .ok forms => decide (forms = expected)
  | .error _ => false

private def parseLineErr? (spec : MeTTailCore.MeTTaSyntax.SyntaxSpec)
    (line : String) : Bool :=
  match parseLineWith spec line with
  | .ok _ => false
  | .error _ => true

/-- Compatibility profile preserves the historical `!name` symbol quirk. -/
def compatibilityBangPrefixedWordIsSymbol : Bool :=
  parseLineOk? heCompatibilitySyntaxSpec "!name" (.fact (sym "!name"))

/-- Canonical profile removes the `!name` symbol quirk and treats `!` as eval. -/
def canonicalBangPrefixedWordIsEval : Bool :=
  parseLineOk? heCanonicalSyntaxSpec "!name" (.eval (sym "name"))

/-- HE compatibility profile accepts eval-prefix followed by a newline. -/
def compatibilityEvalPrefixNewlineForm : Bool :=
  parseProgramOk? heCompatibilitySyntaxSpec "!\n(foo)\n"
    [(1, .eval (app "foo" []))]

/-- HE compatibility profile accepts delimiter comments after a bare eval prefix. -/
def compatibilityEvalPrefixNewlineCommentForm : Bool :=
  parseProgramOk? heCompatibilitySyntaxSpec "!\n; inline comment\n(foo)\n"
    [(1, .eval (app "foo" []))]

/-- Plain comment lines are treated as empty statements. -/
def compatibilityCommentOnlyLineEmpty : Bool :=
  parseLineOk? heCompatibilitySyntaxSpec "; comment only" .empty

/-- Bare `!` without a payload is still a parse error in both profiles. -/
def compatibilityBareBangRejected : Bool :=
  parseLineErr? heCompatibilitySyntaxSpec "!"

/-- The canonical profile keeps ordinary equation syntax unchanged. -/
def canonicalDefineEqForm : Bool :=
  parseLineOk? heCanonicalSyntaxSpec "(= (f a) b)"
    (.defineEq (app "f" [sym "a"]) (sym "b"))

/-- The compatibility profile keeps ordinary type-assignment syntax unchanged. -/
def compatibilityDefineTypeForm : Bool :=
  parseLineOk? heCompatibilitySyntaxSpec "(: foo Bar)"
    (.defineType (sym "foo") (sym "Bar"))

/-- Both profiles keep the existing `match` eval-space alias syntax shape. -/
def canonicalEvalSpaceAliasMatchForm : Bool :=
  parseLineOk? heCanonicalSyntaxSpec "(match &self foo foo)"
    (.fact (app "match" [sym "&self", sym "foo", sym "foo"]))

def allChecks : List (String × Bool) :=
  [ ("compatibilityBangPrefixedWordIsSymbol", compatibilityBangPrefixedWordIsSymbol)
  , ("canonicalBangPrefixedWordIsEval", canonicalBangPrefixedWordIsEval)
  , ("compatibilityEvalPrefixNewlineForm", compatibilityEvalPrefixNewlineForm)
  , ("compatibilityEvalPrefixNewlineCommentForm", compatibilityEvalPrefixNewlineCommentForm)
  , ("compatibilityCommentOnlyLineEmpty", compatibilityCommentOnlyLineEmpty)
  , ("compatibilityBareBangRejected", compatibilityBareBangRejected)
  , ("canonicalDefineEqForm", canonicalDefineEqForm)
  , ("compatibilityDefineTypeForm", compatibilityDefineTypeForm)
  , ("canonicalEvalSpaceAliasMatchForm", canonicalEvalSpaceAliasMatchForm)
  ]

/-- Aggregate executable parser-conformance status for the curated HE fixtures. -/
def allChecksPass : Bool :=
  allChecks.all Prod.snd

end Mettapedia.Conformance.HEParserConformance
