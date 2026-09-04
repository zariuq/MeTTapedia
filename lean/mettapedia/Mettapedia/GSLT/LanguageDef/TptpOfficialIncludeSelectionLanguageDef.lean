import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionResultCarrier
import Mettapedia.GSLT.LanguageDef.PatternEqualityDecision
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Declared TPTP include-selection machine

TPTP include selection is applied after recursively expanding the target
source.  This `LanguageDef` makes that algorithm operational: duplicate request
names are rejected, selected formulae retain source order, every requested name
must occur, and a second matching formula occurrence is rejected.

Structural pattern equality is supplied by the generic, total
`PatternEqualityDecision` relation.  The rules otherwise manipulate only the
typed include-resolution result carrier.  They do not read files, follow
include edges, or invoke the host `applySelection` function.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution

namespace ResultCarrier

abbrev language :=
  TptpOfficialIncludeResolutionResultCarrier.language
abbrev encodeString :=
  TptpOfficialIncludeResolutionResultCarrier.encodeString
abbrev encodeFormulaSelection :=
  TptpOfficialIncludeResolutionResultCarrier.encodeFormulaSelection
abbrev encodeResolvedFormulas :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolvedFormulas
abbrev encodeResolutionError :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolutionError

end ResultCarrier

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def v (name : String) : Pattern := .fvar name

def typed (entries : List (String × String)) : List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

def ctor (label category : String) (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
  evalPolicy? := policy
}

def mkRule (name : String) (context : List (String × String))
    (premises : List Premise) (left right : Pattern) : RewriteRule := {
  name
  typeContext := typed context
  premises
  left
  right
}

def congruence (source target : Pattern) : Premise :=
  .congruence source target

def stringsNil : Pattern :=
  a "tptp-include-result:strings-nil"

def stringsCons (head tail : Pattern) : Pattern :=
  a "tptp-include-result:strings-cons" [head, tail]

def noString : Pattern :=
  a "tptp-include-result:no-string"

def someString (value : Pattern) : Pattern :=
  a "tptp-include-result:some-string" [value]

def selectionImplicitAll : Pattern :=
  a "tptp-include-result:selection-implicit-all"

def selectionExplicitAll : Pattern :=
  a "tptp-include-result:selection-explicit-all"

def selectionNamed (names : Pattern) : Pattern :=
  a "tptp-include-result:selection-named" [names]

def formulasNil : Pattern :=
  a "tptp-include-result:resolved-formulas-nil"

def formulasCons (head tail : Pattern) : Pattern :=
  a "tptp-include-result:resolved-formulas-cons" [head, tail]

def resolvedFormula (name input origin : Pattern) : Pattern :=
  a "tptp-include-result:resolved-formula" [name, input, origin]

def errorDuplicate (target name : Pattern) : Pattern :=
  a "tptp-include-result:error-duplicate-selection-name" [target, name]

def errorMissing (target name : Pattern) : Pattern :=
  a "tptp-include-result:error-missing-selection-name" [target, name]

def errorAmbiguous (target name : Pattern) : Pattern :=
  a "tptp-include-result:error-ambiguous-selection-name" [target, name]

def boolFalse : Pattern := a "tptp-include-selection:false"
def boolTrue : Pattern := a "tptp-include-selection:true"

def selectionOk (formulas : Pattern) : Pattern :=
  a "tptp-include-selection:ok" [formulas]

def selectionError (failure : Pattern) : Pattern :=
  a "tptp-include-selection:error" [failure]

def contains (needle strings : Pattern) : Pattern :=
  a "tptp-include-selection:contains" [needle, strings]

def containsDecision (decision needle tail : Pattern) : Pattern :=
  a "tptp-include-selection:contains-decision" [decision, needle, tail]

def firstDuplicate (strings : Pattern) : Pattern :=
  a "tptp-include-selection:first-duplicate" [strings]

def firstDuplicateDecision (membership head tail : Pattern) : Pattern :=
  a "tptp-include-selection:first-duplicate-decision"
    [membership, head, tail]

def eraseFirst (needle strings : Pattern) : Pattern :=
  a "tptp-include-selection:erase-first" [needle, strings]

def eraseFirstDecision (decision needle head tail : Pattern) : Pattern :=
  a "tptp-include-selection:erase-first-decision"
    [decision, needle, head, tail]

def prepend (formula outcome : Pattern) : Pattern :=
  a "tptp-include-selection:prepend" [formula, outcome]

def scan (target requested remaining seen formulas : Pattern) : Pattern :=
  a "tptp-include-selection:scan"
    [target, requested, remaining, seen, formulas]

def scanRequestDecision (membership target requested remaining seen formula
    formulas : Pattern) : Pattern :=
  a "tptp-include-selection:scan-request-decision"
    [membership, target, requested, remaining, seen, formula, formulas]

def scanSeenDecision (membership target requested remaining seen formula
    formulas : Pattern) : Pattern :=
  a "tptp-include-selection:scan-seen-decision"
    [membership, target, requested, remaining, seen, formula, formulas]

def applySelection (target selection formulas : Pattern) : Pattern :=
  a "tptp-include-selection:apply" [target, selection, formulas]

def namedDecision (duplicate target requested formulas : Pattern) : Pattern :=
  a "tptp-include-selection:named-decision"
    [duplicate, target, requested, formulas]

def supportTypes : List TypeDecl := [
  TypeDecl.plain "TptpIncludeSelection:Bool",
  TypeDecl.plain "TptpIncludeSelection:Outcome"]

def supportTerms : List GrammarRule := [
  ctor "tptp-include-selection:false" "TptpIncludeSelection:Bool" [],
  ctor "tptp-include-selection:true" "TptpIncludeSelection:Bool" [],
  ctor "tptp-include-selection:ok" "TptpIncludeSelection:Outcome"
    [("formulas", "TptpIncludeResult:ResolvedFormulas")],
  ctor "tptp-include-selection:error" "TptpIncludeSelection:Outcome"
    [("failure", "TptpIncludeResult:ResolutionError")],
  ctor "tptp-include-selection:contains" "TptpIncludeSelection:Bool"
    [("needle", "String"), ("strings", "TptpIncludeResult:Strings")]
    (some .rewrite),
  ctor "tptp-include-selection:contains-decision"
    "TptpIncludeSelection:Bool"
    [("decision", "PatternEqualityDecision:Result"), ("needle", "String"),
      ("tail", "TptpIncludeResult:Strings")] (some .rewrite),
  ctor "tptp-include-selection:first-duplicate"
    "TptpIncludeResult:OptionalString"
    [("strings", "TptpIncludeResult:Strings")] (some .rewrite),
  ctor "tptp-include-selection:first-duplicate-decision"
    "TptpIncludeResult:OptionalString"
    [("membership", "TptpIncludeSelection:Bool"), ("head", "String"),
      ("tail", "TptpIncludeResult:Strings")] (some .rewrite),
  ctor "tptp-include-selection:erase-first"
    "TptpIncludeResult:Strings"
    [("needle", "String"), ("strings", "TptpIncludeResult:Strings")]
    (some .rewrite),
  ctor "tptp-include-selection:erase-first-decision"
    "TptpIncludeResult:Strings"
    [("decision", "PatternEqualityDecision:Result"), ("needle", "String"),
      ("head", "String"), ("tail", "TptpIncludeResult:Strings")]
    (some .rewrite),
  ctor "tptp-include-selection:prepend" "TptpIncludeSelection:Outcome"
    [("formula", "TptpIncludeResult:ResolvedFormula"),
      ("outcome", "TptpIncludeSelection:Outcome")] (some .rewrite),
  ctor "tptp-include-selection:scan" "TptpIncludeSelection:Outcome"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] (some .rewrite),
  ctor "tptp-include-selection:scan-request-decision"
    "TptpIncludeSelection:Outcome"
    [("membership", "TptpIncludeSelection:Bool"), ("target", "String"),
      ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("formula", "TptpIncludeResult:ResolvedFormula"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] (some .rewrite),
  ctor "tptp-include-selection:scan-seen-decision"
    "TptpIncludeSelection:Outcome"
    [("membership", "TptpIncludeSelection:Bool"), ("target", "String"),
      ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("formula", "TptpIncludeResult:ResolvedFormula"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] (some .rewrite),
  ctor "tptp-include-selection:apply" "TptpIncludeSelection:Outcome"
    [("target", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] (some .rewrite),
  ctor "tptp-include-selection:named-decision"
    "TptpIncludeSelection:Outcome"
    [("duplicate", "TptpIncludeResult:OptionalString"),
      ("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] (some .rewrite)]

def containsRules : List RewriteRule := [
  mkRule "tptp-include-selection:contains-nil"
    [("needle", "String")] []
    (contains (v "needle") stringsNil) boolFalse,
  mkRule "tptp-include-selection:contains-cons"
    [("needle", "String"), ("head", "String"),
      ("tail", "TptpIncludeResult:Strings"),
      ("decision", "PatternEqualityDecision:Result"),
      ("result", "TptpIncludeSelection:Bool")]
    [.relationQuery PatternEqualityDecision.relationName
        [v "needle", v "head", v "decision"],
      congruence
        (containsDecision (v "decision") (v "needle") (v "tail"))
        (v "result")]
    (contains (v "needle") (stringsCons (v "head") (v "tail")))
    (v "result"),
  mkRule "tptp-include-selection:contains-equal"
    [("needle", "String"), ("tail", "TptpIncludeResult:Strings")] []
    (containsDecision PatternEqualityDecision.equal
      (v "needle") (v "tail")) boolTrue,
  mkRule "tptp-include-selection:contains-different"
    [("needle", "String"), ("tail", "TptpIncludeResult:Strings"),
      ("result", "TptpIncludeSelection:Bool")]
    [congruence (contains (v "needle") (v "tail")) (v "result")]
    (containsDecision PatternEqualityDecision.different
      (v "needle") (v "tail")) (v "result")]

def duplicateRules : List RewriteRule := [
  mkRule "tptp-include-selection:duplicate-nil" [] []
    (firstDuplicate stringsNil) noString,
  mkRule "tptp-include-selection:duplicate-cons"
    [("head", "String"), ("tail", "TptpIncludeResult:Strings"),
      ("membership", "TptpIncludeSelection:Bool"),
      ("result", "TptpIncludeResult:OptionalString")]
    [congruence (contains (v "head") (v "tail")) (v "membership"),
      congruence
        (firstDuplicateDecision (v "membership") (v "head") (v "tail"))
        (v "result")]
    (firstDuplicate (stringsCons (v "head") (v "tail"))) (v "result"),
  mkRule "tptp-include-selection:duplicate-found"
    [("head", "String"), ("tail", "TptpIncludeResult:Strings")] []
    (firstDuplicateDecision boolTrue (v "head") (v "tail"))
    (someString (v "head")),
  mkRule "tptp-include-selection:duplicate-continue"
    [("head", "String"), ("tail", "TptpIncludeResult:Strings"),
      ("result", "TptpIncludeResult:OptionalString")]
    [congruence (firstDuplicate (v "tail")) (v "result")]
    (firstDuplicateDecision boolFalse (v "head") (v "tail"))
    (v "result")]

def eraseRules : List RewriteRule := [
  mkRule "tptp-include-selection:erase-nil"
    [("needle", "String")] []
    (eraseFirst (v "needle") stringsNil) stringsNil,
  mkRule "tptp-include-selection:erase-cons"
    [("needle", "String"), ("head", "String"),
      ("tail", "TptpIncludeResult:Strings"),
      ("decision", "PatternEqualityDecision:Result"),
      ("result", "TptpIncludeResult:Strings")]
    [.relationQuery PatternEqualityDecision.relationName
        [v "needle", v "head", v "decision"],
      congruence
        (eraseFirstDecision (v "decision") (v "needle")
          (v "head") (v "tail")) (v "result")]
    (eraseFirst (v "needle") (stringsCons (v "head") (v "tail")))
    (v "result"),
  mkRule "tptp-include-selection:erase-equal"
    [("needle", "String"), ("head", "String"),
      ("tail", "TptpIncludeResult:Strings")] []
    (eraseFirstDecision PatternEqualityDecision.equal
      (v "needle") (v "head") (v "tail")) (v "tail"),
  mkRule "tptp-include-selection:erase-different"
    [("needle", "String"), ("head", "String"),
      ("tail", "TptpIncludeResult:Strings"),
      ("erased", "TptpIncludeResult:Strings")]
    [congruence (eraseFirst (v "needle") (v "tail")) (v "erased")]
    (eraseFirstDecision PatternEqualityDecision.different
      (v "needle") (v "head") (v "tail"))
    (stringsCons (v "head") (v "erased"))]

def scanFinishedRule : RewriteRule :=
  mkRule "tptp-include-selection:scan-finished"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings")] []
    (scan (v "target") (v "requested") stringsNil (v "seen") formulasNil)
    (selectionOk formulasNil)

def scanMissingRule : RewriteRule :=
  mkRule "tptp-include-selection:scan-missing"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("missing", "String"), ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings")] []
    (scan (v "target") (v "requested")
      (stringsCons (v "missing") (v "remaining")) (v "seen") formulasNil)
    (selectionError (errorMissing (v "target") (v "missing")))

def scanConsRule : RewriteRule :=
  mkRule "tptp-include-selection:scan-cons"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("name", "String"), ("input", "Tptp92Ast:tptp-input"),
      ("origin", "TptpIncludeResult:FormulaOrigin"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("membership", "TptpIncludeSelection:Bool"),
      ("result", "TptpIncludeSelection:Outcome")]
    [congruence (contains (v "name") (v "requested")) (v "membership"),
      congruence
        (scanRequestDecision (v "membership") (v "target")
          (v "requested") (v "remaining") (v "seen")
          (resolvedFormula (v "name") (v "input") (v "origin"))
          (v "formulas")) (v "result")]
    (scan (v "target") (v "requested") (v "remaining") (v "seen")
      (formulasCons
        (resolvedFormula (v "name") (v "input") (v "origin"))
        (v "formulas"))) (v "result")

def scanSkipRule : RewriteRule :=
  mkRule "tptp-include-selection:scan-skip"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("formula", "TptpIncludeResult:ResolvedFormula"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("result", "TptpIncludeSelection:Outcome")]
    [congruence
      (scan (v "target") (v "requested") (v "remaining")
        (v "seen") (v "formulas")) (v "result")]
    (scanRequestDecision boolFalse (v "target") (v "requested")
      (v "remaining") (v "seen") (v "formula") (v "formulas"))
    (v "result")

def scanCheckSeenRule : RewriteRule :=
  mkRule "tptp-include-selection:scan-check-seen"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("name", "String"), ("input", "Tptp92Ast:tptp-input"),
      ("origin", "TptpIncludeResult:FormulaOrigin"),
      ("membership", "TptpIncludeSelection:Bool"),
      ("result", "TptpIncludeSelection:Outcome")]
    [congruence (contains (v "name") (v "seen")) (v "membership"),
      congruence
        (scanSeenDecision (v "membership") (v "target")
          (v "requested") (v "remaining") (v "seen")
          (resolvedFormula (v "name") (v "input") (v "origin"))
          (v "formulas")) (v "result")]
    (scanRequestDecision boolTrue (v "target") (v "requested")
      (v "remaining") (v "seen")
      (resolvedFormula (v "name") (v "input") (v "origin"))
      (v "formulas")) (v "result")

def scanAmbiguousRule : RewriteRule :=
  mkRule "tptp-include-selection:scan-ambiguous"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("name", "String"), ("input", "Tptp92Ast:tptp-input"),
      ("origin", "TptpIncludeResult:FormulaOrigin"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] []
    (scanSeenDecision boolTrue (v "target") (v "requested")
      (v "remaining") (v "seen")
      (resolvedFormula (v "name") (v "input") (v "origin"))
      (v "formulas"))
    (selectionError (errorAmbiguous (v "target") (v "name")))

def scanSelectRule : RewriteRule :=
  mkRule "tptp-include-selection:scan-select"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("remaining", "TptpIncludeResult:Strings"),
      ("seen", "TptpIncludeResult:Strings"),
      ("name", "String"), ("input", "Tptp92Ast:tptp-input"),
      ("origin", "TptpIncludeResult:FormulaOrigin"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("erased", "TptpIncludeResult:Strings"),
      ("rest", "TptpIncludeSelection:Outcome"),
      ("result", "TptpIncludeSelection:Outcome")]
    [congruence (eraseFirst (v "name") (v "remaining")) (v "erased"),
      congruence
        (scan (v "target") (v "requested") (v "erased")
          (stringsCons (v "name") (v "seen")) (v "formulas")) (v "rest"),
      congruence
        (prepend
          (resolvedFormula (v "name") (v "input") (v "origin"))
          (v "rest")) (v "result")]
    (scanSeenDecision boolFalse (v "target") (v "requested")
      (v "remaining") (v "seen")
      (resolvedFormula (v "name") (v "input") (v "origin"))
      (v "formulas")) (v "result")

def prependOkRule : RewriteRule :=
  mkRule "tptp-include-selection:prepend-ok"
    [("formula", "TptpIncludeResult:ResolvedFormula"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] []
    (prepend (v "formula") (selectionOk (v "formulas")))
    (selectionOk (formulasCons (v "formula") (v "formulas")))

def prependErrorRule : RewriteRule :=
  mkRule "tptp-include-selection:prepend-error"
    [("formula", "TptpIncludeResult:ResolvedFormula"),
      ("failure", "TptpIncludeResult:ResolutionError")] []
    (prepend (v "formula") (selectionError (v "failure")))
    (selectionError (v "failure"))

def scanRules : List RewriteRule := [
  scanFinishedRule,
  scanMissingRule,
  scanConsRule,
  scanSkipRule,
  scanCheckSeenRule,
  scanAmbiguousRule,
  scanSelectRule,
  prependOkRule,
  prependErrorRule]

def applyRules : List RewriteRule := [
  mkRule "tptp-include-selection:apply-implicit-all"
    [("target", "String"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] []
    (applySelection (v "target") selectionImplicitAll (v "formulas"))
    (selectionOk (v "formulas")),
  mkRule "tptp-include-selection:apply-explicit-all"
    [("target", "String"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas")] []
    (applySelection (v "target") selectionExplicitAll (v "formulas"))
    (selectionOk (v "formulas")),
  mkRule "tptp-include-selection:apply-named"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("duplicate", "TptpIncludeResult:OptionalString"),
      ("result", "TptpIncludeSelection:Outcome")]
    [congruence (firstDuplicate (v "requested")) (v "duplicate"),
      congruence
        (namedDecision (v "duplicate") (v "target")
          (v "requested") (v "formulas")) (v "result")]
    (applySelection (v "target") (selectionNamed (v "requested"))
      (v "formulas")) (v "result"),
  mkRule "tptp-include-selection:named-duplicate"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("duplicate", "String")] []
    (namedDecision (someString (v "duplicate")) (v "target")
      (v "requested") (v "formulas"))
    (selectionError (errorDuplicate (v "target") (v "duplicate"))),
  mkRule "tptp-include-selection:named-scan"
    [("target", "String"), ("requested", "TptpIncludeResult:Strings"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("result", "TptpIncludeSelection:Outcome")]
    [congruence
      (scan (v "target") (v "requested") (v "requested") stringsNil
        (v "formulas")) (v "result")]
    (namedDecision noString (v "target") (v "requested") (v "formulas"))
    (v "result")]

def rewrites : List RewriteRule :=
  containsRules ++ duplicateRules ++ eraseRules ++ scanRules ++ applyRules

private def addedTypes : List TypeDecl :=
  PatternEqualityDecision.language.types ++ supportTypes

private def addedTerms : List GrammarRule :=
  PatternEqualityDecision.language.terms ++ supportTerms

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend ResultCarrier.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeSelectionV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def language : LanguageDef := {
  name := "TptpOfficialIncludeSelectionV1"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem typeNames_exact :
    language.typeNames = ResultCarrier.language.typeNames ++
      (PatternEqualityDecision.language.types ++ supportTypes).map
        (·.name) := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists,
    addedTypes, LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        ResultCarrier.language ++
      (PatternEqualityDecision.language.terms ++ supportTerms).map fun declaration =>
        (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists, addedTerms]

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

theorem rewrite_count : rewrites.length = 26 := by
  decide +kernel

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.typeNames (addedTypes.map (·.name)) := by
  have baseSeparate :
      signatureBase.typeNames.all
        (fun name =>
          !(name.startsWith "PatternEqualityDecision:") &&
            !(name.startsWith "TptpIncludeSelection:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTypes.map (·.name)).all
        (fun name =>
          name.startsWith "PatternEqualityDecision:" ||
            name.startsWith "TptpIncludeSelection:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  have base := (List.all_eq_true.mp baseSeparate) name baseMembership
  have added := (List.all_eq_true.mp addedNamespaced) name addedMembership
  simp only [Bool.and_eq_true, Bool.or_eq_true] at base added
  rcases base with ⟨notEquality, notSelection⟩
  rcases added with equality | selection
  · simp [equality] at notEquality
  · simp [selection] at notSelection

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.terms.map (·.label))
      (addedTerms.map (·.label)) := by
  have baseSeparate :
      (signatureBase.terms.map (·.label)).all
        (fun label =>
          !(label.startsWith "pattern-equality-decision:") &&
            !(label.startsWith "tptp-include-selection:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTerms.map (·.label)).all
        (fun label =>
          label.startsWith "pattern-equality-decision:" ||
            label.startsWith "tptp-include-selection:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label baseMembership addedMembership
  have base := (List.all_eq_true.mp baseSeparate) label baseMembership
  have added := (List.all_eq_true.mp addedNamespaced) label addedMembership
  simp only [Bool.and_eq_true, Bool.or_eq_true] at base added
  rcases base with ⟨notEquality, notSelection⟩
  rcases added with equality | selection
  · simp [equality] at notEquality
  · simp [selection] at notSelection

private theorem added_terms_validate_all :
    addedTerms.all (fun term => signatureLanguage.validateTerm term == []) =
      true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) :
    signatureLanguage.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

theorem signatureLanguage_validate : signatureLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    signatureBase addedTypes addedTerms
      (some "TptpOfficialIncludeSelectionV1")
  · simpa [signatureBase] using
      TptpOfficialIncludeResolutionResultCarrier.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

private def requiredTypes : List String := [
  "String", "Tptp92Ast:tptp-input",
  "TptpIncludeResult:Strings", "TptpIncludeResult:FormulaSelection",
  "TptpIncludeResult:OptionalString",
  "TptpIncludeResult:FormulaOrigin",
  "TptpIncludeResult:ResolvedFormula",
  "TptpIncludeResult:ResolvedFormulas",
  "TptpIncludeResult:ResolutionError",
  "PatternEqualityDecision:Result",
  "TptpIncludeSelection:Bool", "TptpIncludeSelection:Outcome"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) =
      true := by
  decide +kernel

private theorem requiredType_declared (name : String)
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredTypes_declared name membership)

private def requiredSignatures : List (String × Nat) := [
  ("tptp-include-result:strings-nil", 0),
  ("tptp-include-result:strings-cons", 2),
  ("tptp-include-result:no-string", 0),
  ("tptp-include-result:some-string", 1),
  ("tptp-include-result:selection-implicit-all", 0),
  ("tptp-include-result:selection-explicit-all", 0),
  ("tptp-include-result:selection-named", 1),
  ("tptp-include-result:resolved-formulas-nil", 0),
  ("tptp-include-result:resolved-formulas-cons", 2),
  ("tptp-include-result:resolved-formula", 3),
  ("tptp-include-result:error-duplicate-selection-name", 2),
  ("tptp-include-result:error-missing-selection-name", 2),
  ("tptp-include-result:error-ambiguous-selection-name", 2),
  ("pattern-equality-decision:equal", 0),
  ("pattern-equality-decision:different", 0),
  ("tptp-include-selection:false", 0),
  ("tptp-include-selection:true", 0),
  ("tptp-include-selection:ok", 1),
  ("tptp-include-selection:error", 1),
  ("tptp-include-selection:contains", 2),
  ("tptp-include-selection:contains-decision", 3),
  ("tptp-include-selection:first-duplicate", 1),
  ("tptp-include-selection:first-duplicate-decision", 3),
  ("tptp-include-selection:erase-first", 2),
  ("tptp-include-selection:erase-first-decision", 4),
  ("tptp-include-selection:prepend", 2),
  ("tptp-include-selection:scan", 5),
  ("tptp-include-selection:scan-request-decision", 7),
  ("tptp-include-selection:scan-seen-decision", 7),
  ("tptp-include-selection:apply", 3),
  ("tptp-include-selection:named-decision", 4)]

private theorem requiredSignatures_declared :
    requiredSignatures.all (fun signature => decide
      (signature ∈ RewriteValidationCertificate.constructorSignatures
        language)) = true := by
  decide +kernel

private theorem requiredSignature_declared
    (signature : String × Nat) (membership : signature ∈ requiredSignatures) :
    signature ∈ RewriteValidationCertificate.constructorSignatures language :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredSignatures_declared signature membership)

def constructorLabelReserved (label : String) : Bool :=
  label.startsWith "tptp" ||
    label.startsWith "pattern-equality-decision:"

private theorem constructorLabels_reserved :
    (RewriteValidationCertificate.constructorLabels language).all
      constructorLabelReserved = true := by
  decide +kernel

private theorem plainName_not_constructor (name : String)
    (plain : constructorLabelReserved name = false) :
    name ∉ RewriteValidationCertificate.constructorLabels language := by
  intro membership
  have reserved := (List.all_eq_true.mp constructorLabels_reserved)
    name membership
  simp [plain] at reserved

private def contextSubsetCheck (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    entry.2.baseNames.all fun name => decide (name ∈ requiredTypes)

private def patternSubsetCheck (pattern : Pattern) : Bool :=
  pattern.constructorRefs.all fun signature =>
    decide (signature ∈ requiredSignatures)

private def premisesSubsetCheck (rewrite : RewriteRule) : Bool :=
  (rewrite.premises.flatMap LanguageDef.premisePatterns).all
    patternSubsetCheck

private def fvarsPlainCheck (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternFvarNames [] rewrite.left ++
    LanguageDef.patternFvarNames [] rewrite.right ++
    rewrite.premises.flatMap
      (LanguageDef.premiseFvarNames [])).eraseDups).all fun name =>
    !constructorLabelReserved name

private def bindersPlainCheck (rewrite : RewriteRule) : Bool :=
  ((LanguageDef.patternBinderNames rewrite.left ++
    LanguageDef.patternBinderNames rewrite.right ++
    (rewrite.premises.flatMap LanguageDef.premisePatterns).flatMap
      LanguageDef.patternBinderNames ++
    rewrite.premises.flatMap
      LanguageDef.premiseForAllParams).eraseDups).all fun name =>
    !constructorLabelReserved name

private def contextNamesPlainCheck (rewrite : RewriteRule) : Bool :=
  rewrite.typeContext.all fun entry =>
    !constructorLabelReserved entry.1

private def subsetCheck (rewrite : RewriteRule) : Bool :=
  contextSubsetCheck rewrite &&
    (patternSubsetCheck rewrite.left &&
      (patternSubsetCheck rewrite.right &&
        (premisesSubsetCheck rewrite &&
          (RewriteValidationCertificate.allPatternsScopedCheck rewrite &&
            (fvarsPlainCheck rewrite &&
              (bindersPlainCheck rewrite &&
                (contextNamesPlainCheck rewrite &&
                  RewriteValidationCertificate.rightBoundCheck rewrite)))))))

private theorem certificate_of_subsetCheck {rewrite : RewriteRule}
    (checked : subsetCheck rewrite = true) :
    RewriteValidationCertificate.Certificate language rewrite := by
  simp only [subsetCheck, Bool.and_eq_true] at checked
  rcases checked with
    ⟨contextChecked, leftChecked, rightChecked, premisesChecked,
      scopedChecked, fvarsChecked, bindersChecked, contextNamesChecked,
      rightBoundedChecked⟩
  simp only [contextSubsetCheck] at contextChecked
  simp only [patternSubsetCheck] at leftChecked rightChecked
  simp only [premisesSubsetCheck] at premisesChecked
  simp only [fvarsPlainCheck] at fvarsChecked
  simp only [bindersPlainCheck] at bindersChecked
  simp only [contextNamesPlainCheck] at contextNamesChecked
  refine {
    contextTypes := ?_
    leftDeclared := ?_
    rightDeclared := ?_
    premisesDeclared := ?_
    allPatternsScoped := scopedChecked
    fvarsAvoidConstructors := ?_
    bindersAvoidConstructors := ?_
    contextAvoidsConstructors := ?_
    rightBound := ?_ }
  · intro entry entryMembership name nameMembership
    apply requiredType_declared name
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp contextChecked entry entryMembership)
      name nameMembership)
  · intro signature signatureMembership
    apply requiredSignature_declared signature
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp leftChecked signature signatureMembership)
  · intro signature signatureMembership
    apply requiredSignature_declared signature
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightChecked signature signatureMembership)
  · intro pattern patternMembership signature signatureMembership
    apply requiredSignature_declared signature
    exact decide_eq_true_eq.mp (List.all_eq_true.mp
      (List.all_eq_true.mp premisesChecked pattern patternMembership)
      signature signatureMembership)
  · intro name nameMembership
    apply plainName_not_constructor name
    have plain := List.all_eq_true.mp fvarsChecked name nameMembership
    simpa using plain
  · intro name nameMembership
    apply plainName_not_constructor name
    have plain := List.all_eq_true.mp bindersChecked name nameMembership
    simpa using plain
  · intro entry entryMembership
    apply plainName_not_constructor entry.1
    have plain := List.all_eq_true.mp contextNamesChecked entry entryMembership
    simpa using plain
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightBoundedChecked name nameMembership)

local macro "certify_subset_rows" : tactic =>
  `(tactic|
    simp [subsetCheck, contextSubsetCheck, patternSubsetCheck,
      premisesSubsetCheck, fvarsPlainCheck, bindersPlainCheck,
      contextNamesPlainCheck, containsRules, duplicateRules, eraseRules,
      scanRules, scanFinishedRule, scanMissingRule, scanConsRule,
      scanSkipRule, scanCheckSeenRule, scanAmbiguousRule, scanSelectRule,
      prependOkRule, prependErrorRule, applyRules, contains, containsDecision, firstDuplicate,
      firstDuplicateDecision, eraseFirst, eraseFirstDecision, prepend, scan,
      scanRequestDecision, scanSeenDecision, applySelection, namedDecision,
      stringsNil, stringsCons, noString, someString, selectionImplicitAll,
      selectionExplicitAll, selectionNamed, formulasNil, formulasCons,
      resolvedFormula, errorDuplicate, errorMissing, errorAmbiguous,
      boolFalse, boolTrue, selectionOk, selectionError, mkRule,
      congruence, typed, a, v, LanguageDef.premisePatterns,
      LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
      Pattern.constructorRefs, Pattern.constructorRefsList,
      Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead, requiredTypes,
      requiredSignatures, constructorLabelReserved,
      PatternEqualityDecision.equal, PatternEqualityDecision.different,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.rightBoundCheck])

private theorem contains_subset_checked :
    containsRules.all subsetCheck = true := by
  certify_subset_rows

private theorem duplicate_subset_checked :
    duplicateRules.all subsetCheck = true := by
  certify_subset_rows

private theorem erase_subset_checked :
    eraseRules.all subsetCheck = true := by
  certify_subset_rows

private theorem scan_finished_subset_checked :
    subsetCheck scanFinishedRule = true := by certify_subset_rows

private theorem scan_missing_subset_checked :
    subsetCheck scanMissingRule = true := by certify_subset_rows

private theorem scan_cons_subset_checked :
    subsetCheck scanConsRule = true := by certify_subset_rows

private theorem scan_skip_subset_checked :
    subsetCheck scanSkipRule = true := by certify_subset_rows

private theorem scan_check_seen_subset_checked :
    subsetCheck scanCheckSeenRule = true := by certify_subset_rows

private theorem scan_ambiguous_subset_checked :
    subsetCheck scanAmbiguousRule = true := by certify_subset_rows

private theorem scan_select_subset_checked :
    subsetCheck scanSelectRule = true := by certify_subset_rows

private theorem prepend_ok_subset_checked :
    subsetCheck prependOkRule = true := by certify_subset_rows

private theorem prepend_error_subset_checked :
    subsetCheck prependErrorRule = true := by certify_subset_rows

private theorem scan_subset_checked :
    scanRules.all subsetCheck = true := by
  simp only [scanRules, List.all_cons, List.all_nil,
    scan_finished_subset_checked, scan_missing_subset_checked,
    scan_cons_subset_checked, scan_skip_subset_checked,
    scan_check_seen_subset_checked, scan_ambiguous_subset_checked,
    scan_select_subset_checked, prepend_ok_subset_checked,
    prepend_error_subset_checked, Bool.and_self]

private theorem apply_subset_checked :
    applyRules.all subsetCheck = true := by
  certify_subset_rows

private theorem every_rewrite_subset_checked :
    rewrites.all subsetCheck = true := by
  simp only [rewrites, List.all_append, contains_subset_checked,
    duplicate_subset_checked, erase_subset_checked, scan_subset_checked,
    apply_subset_checked, Bool.and_self]

/-- Reusable row certificate for capture-free linking. -/
theorem rewrite_certificate (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    RewriteValidationCertificate.Certificate language rewrite :=
  certificate_of_subsetCheck
    (List.all_eq_true.mp every_rewrite_subset_checked rewrite membership)

theorem rewrite_schema_names_unreserved (rewrite : RewriteRule)
    (membership : rewrite ∈ rewrites) :
    (RewriteValidationCertificateExtension.schemaNames rewrite).all
      (fun name => !constructorLabelReserved name) = true := by
  have checked :=
    List.all_eq_true.mp every_rewrite_subset_checked rewrite membership
  simp only [subsetCheck, Bool.and_eq_true] at checked
  rcases checked with
    ⟨_contextChecked, _leftChecked, _rightChecked, _premisesChecked,
      _scopedChecked, fvarsChecked, bindersChecked, contextNamesChecked,
      _rightBoundedChecked⟩
  simp only [fvarsPlainCheck] at fvarsChecked
  simp only [bindersPlainCheck] at bindersChecked
  simp only [contextNamesPlainCheck] at contextNamesChecked
  exact RewriteValidationCertificateExtension.schemaNames_all_of_components
    rewrite (fun name => !constructorLabelReserved name)
      fvarsChecked bindersChecked contextNamesChecked

private theorem language_constructor_labels_nodup :
    (language.terms.map (·.label)).Nodup := by
  simpa [language] using
    LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate

private theorem rewrites_valid :
    ∀ rewrite ∈ rewrites, language.validateRewrite rewrite = [] := by
  intro rewrite membership
  apply RewriteValidationCertificate.validateRewrite_eq_nil
    language_constructor_labels_nodup
  apply certificate_of_subsetCheck
  exact List.all_eq_true.mp every_rewrite_subset_checked rewrite membership

private theorem rewrite_names_nodup :
    (rewrites.map (·.name)).Nodup := by
  decide +kernel

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · exact LanguageDef.typeNames_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate
  · simp [language]
  · exact rewrite_names_nodup
  · intro term membership
    exact LanguageDef.validateTerm_eq_nil_of_validate_eq_nil
      signatureLanguage signatureLanguage_validate term membership
  · intro equation membership
    simp [language] at membership
  · exact rewrites_valid

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

private theorem base_supported :
    CanonicalWire.languageSupported ResultCarrier.language :=
  TptpOfficialIncludeResolutionResultCarrier.language_supported

private theorem language_terms :
    language.terms = ResultCarrier.language.terms ++ addedTerms := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists]

private theorem terms_supported :
    language.terms.all CanonicalWire.grammarRuleSupported = true := by
  have source := base_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at source
  rw [language_terms, List.all_append]
  rw [Bool.and_eq_true]
  exact ⟨source.1.2, by decide +kernel⟩

private theorem rewrites_supported :
    language.rewrites.all CanonicalWire.rewriteSupported = true := by
  decide +kernel

theorem language_supported : CanonicalWire.languageSupported language := by
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, terms_supported⟩, rewrites_supported⟩

def relations : RelationEnv := PatternEqualityDecision.relationEnv

def encodeOutcome :
    Except ResolutionError (List ResolvedFormula) -> Pattern
  | .error failure =>
      selectionError (ResultCarrier.encodeResolutionError failure)
  | .ok formulas =>
      selectionOk (ResultCarrier.encodeResolvedFormulas formulas)

def encodeRequest (target : String) (selection : FormulaSelection)
    (formulas : List ResolvedFormula) : Pattern :=
  applySelection (ResultCarrier.encodeString target)
    (ResultCarrier.encodeFormulaSelection selection)
    (ResultCarrier.encodeResolvedFormulas formulas)

namespace Canary

def origin : FormulaOrigin := {
  sourceId := "leaf"
  sourceDigest := "leaf-digest"
  sourceInputIndex := 0
  includePath := []
}

def formula (name : String) (index : Nat) : ResolvedFormula := {
  name
  input := TptpOfficialIncludeResolution.Canary.formulaInput name index
  origin := { origin with sourceInputIndex := index }
}

def orderedFormulas : List ResolvedFormula :=
  [formula "a" 0, formula "b" 1, formula "c" 2]

def ambiguousFormulas : List ResolvedFormula :=
  [formula "a" 0, formula "a" 1]

end Canary

#print axioms rewrite_count
#print axioms language_validate
#print axioms language_supported

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeSelectionLanguageDef
