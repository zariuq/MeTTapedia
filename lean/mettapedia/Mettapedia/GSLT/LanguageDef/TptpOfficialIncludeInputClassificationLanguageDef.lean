import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionResultCarrier
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Declared classification of official TPTP include-resolution inputs

Recursive include resolution treats each admitted top-level input as either an
annotated formula or an include directive.  This `LanguageDef` performs that
one-input classification for every official formula family.  Formula results
retain the complete official input and acquire source provenance; include
results retain the exact directive and source span for later path resolution.

The operation does not read files, follow include edges, decode directives, or
apply selections.  Those remain separately qualified transformations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

namespace Carrier

abbrev language :=
  TptpOfficialIncludeResolutionResultCarrier.language

end Carrier

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

def decodeName (source : Pattern) : Pattern :=
  a "tptp-include-input:decode-name" [source]

def decodedName (name : Pattern) : Pattern :=
  a "tptp-include-input:decoded-name" [name]

def classify (sourceId sourceDigest inputIndex path input : Pattern) : Pattern :=
  a "tptp-include-input:classify"
    [sourceId, sourceDigest, inputIndex, path, input]

def inspectFormula (origin input : Pattern) : Pattern :=
  a "tptp-include-input:inspect-formula" [origin, input]

def decodeFormula (origin sourceName input : Pattern) : Pattern :=
  a "tptp-include-input:decode-formula" [origin, sourceName, input]

def formulaOutcome (formula : Pattern) : Pattern :=
  a "tptp-include-input:formula" [formula]

def includeOutcome (directive span : Pattern) : Pattern :=
  a "tptp-include-input:include" [directive, span]

def formulaOrigin (sourceId sourceDigest inputIndex path : Pattern) : Pattern :=
  a "tptp-include-result:formula-origin"
    [sourceId, sourceDigest, inputIndex, path]

def resolvedFormula (name input origin : Pattern) : Pattern :=
  a "tptp-include-result:resolved-formula" [name, input, origin]

def sourceToken (tokenLabel : String) (lexeme : Pattern) : Pattern :=
  a tokenLabel [lexeme]

def sourceAtomicWord (alternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  a alternative [sourceToken tokenLabel lexeme]

def sourceNameWord (alternative tokenLabel : String)
    (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:name:alt-1"
    [sourceAtomicWord alternative tokenLabel lexeme]

def sourceIntegerName (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:name:alt-2"
    [sourceToken "tptp92-ast:token:integer" lexeme]

def nameWordRule (name alternative tokenLabel : String) : RewriteRule :=
  mkRule name [("lexeme", "String")] []
    (decodeName (sourceNameWord alternative tokenLabel (v "lexeme")))
    (decodedName (v "lexeme"))

def nameIntegerRule : RewriteRule :=
  mkRule "tptp-include-input:name-integer" [("lexeme", "String")] []
    (decodeName (sourceIntegerName (v "lexeme")))
    (decodedName (v "lexeme"))

def annotatedFormula (wrapperLabel annotatedLabel : String)
    (name role body annotations : Pattern) : Pattern :=
  a wrapperLabel [a annotatedLabel [name, role, body, annotations]]

def locatedFormulaInput (wrapperLabel annotatedLabel : String)
    (name role body annotations span : Pattern) : Pattern :=
  a "tptp92-ast:tptp-input:alt-1"
    [annotatedFormula wrapperLabel annotatedLabel name role body annotations,
      span]

def sourceSpan (start stop : Pattern) : Pattern :=
  a "tptp92-ast:source-span" [start, stop]

def classifyFormulaRule : RewriteRule :=
  let input := a "tptp92-ast:tptp-input:alt-1"
    [v "annotated", sourceSpan (v "start") (v "stop")]
  mkRule "tptp-include-input:classify-formula"
    [("sourceId", "String"), ("sourceDigest", "String"),
      ("inputIndex", "Integer"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("annotated", "Tptp92Ast:annotated-formula"),
      ("start", "Integer"), ("stop", "Integer")]
    []
    (classify (v "sourceId") (v "sourceDigest") (v "inputIndex")
      (v "path") input)
    (inspectFormula
      (formulaOrigin (v "sourceId") (v "sourceDigest") (v "inputIndex")
        (v "path")) input)

def inspectFormulaRule (ruleName wrapperLabel annotatedLabel bodyType : String) :
    RewriteRule :=
  let annotated := annotatedFormula wrapperLabel annotatedLabel
    (v "sourceName") (v "role") (v "body") (v "annotations")
  let input := a "tptp92-ast:tptp-input:alt-1" [annotated, v "span"]
  mkRule ruleName
    [("origin", "TptpIncludeResult:FormulaOrigin"),
      ("sourceName", "Tptp92Ast:name"),
      ("role", "Tptp92Ast:formula-role"), ("body", bodyType),
      ("annotations", "Tptp92Ast:annotations"),
      ("span", "Tptp92Ast:source-span")] []
    (inspectFormula (v "origin") input)
    (decodeFormula (v "origin") (v "sourceName") input)

def finalizeFormulaRule : RewriteRule :=
  mkRule "tptp-include-input:finalize-formula"
    [("origin", "TptpIncludeResult:FormulaOrigin"),
      ("sourceName", "Tptp92Ast:name"),
      ("input", "Tptp92Ast:tptp-input"), ("name", "String")]
    [congruence (decodeName (v "sourceName"))
      (decodedName (v "name"))]
    (decodeFormula (v "origin") (v "sourceName") (v "input"))
    (formulaOutcome
      (resolvedFormula (v "name") (v "input")
        (v "origin")))

def includeRule : RewriteRule :=
  let input := a "tptp92-ast:tptp-input:alt-2"
    [v "directive", sourceSpan (v "start") (v "stop")]
  mkRule "tptp-include-input:include"
    [("sourceId", "String"), ("sourceDigest", "String"),
      ("inputIndex", "Integer"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("directive", "Tptp92Ast:include"),
      ("start", "Integer"), ("stop", "Integer")] []
    (classify (v "sourceId") (v "sourceDigest") (v "inputIndex")
      (v "path") input)
    (includeOutcome (v "directive")
      (sourceSpan (v "start") (v "stop")))

def nameRules : List RewriteRule := [
  nameWordRule "tptp-include-input:name-lower"
    "tptp92-ast:atomic-word:alt-1" "tptp92-ast:token:lower-word",
  nameWordRule "tptp-include-input:name-single-quoted"
    "tptp92-ast:atomic-word:alt-2" "tptp92-ast:token:single-quoted",
  nameWordRule "tptp-include-input:name-back-quoted"
    "tptp92-ast:atomic-word:alt-3" "tptp92-ast:token:back-quoted",
  nameIntegerRule]

def inspectFormulaRules : List RewriteRule := [
  inspectFormulaRule "tptp-include-input:inspect-thf"
    "tptp92-ast:annotated-formula:alt-1"
    "tptp92-ast:thf-annotated:alt-1" "Tptp92Ast:thf-formula",
  inspectFormulaRule "tptp-include-input:inspect-tff"
    "tptp92-ast:annotated-formula:alt-2"
    "tptp92-ast:tff-annotated:alt-1" "Tptp92Ast:tff-formula",
  inspectFormulaRule "tptp-include-input:inspect-tcf"
    "tptp92-ast:annotated-formula:alt-3"
    "tptp92-ast:tcf-annotated:alt-1" "Tptp92Ast:tcf-formula",
  inspectFormulaRule "tptp-include-input:inspect-fof"
    "tptp92-ast:annotated-formula:alt-4"
    "tptp92-ast:fof-annotated:alt-1" "Tptp92Ast:fof-formula",
  inspectFormulaRule "tptp-include-input:inspect-cnf"
    "tptp92-ast:annotated-formula:alt-5"
    "tptp92-ast:cnf-annotated:alt-1" "Tptp92Ast:cnf-formula",
  inspectFormulaRule "tptp-include-input:inspect-tpi"
    "tptp92-ast:annotated-formula:alt-6"
    "tptp92-ast:tpi-annotated:alt-1" "Tptp92Ast:tpi-formula"]

def rewrites : List RewriteRule :=
  nameRules ++ [classifyFormulaRule, includeRule] ++ inspectFormulaRules ++
    [finalizeFormulaRule]

def supportTypes : List TypeDecl := [
  TypeDecl.plain "TptpIncludeInput:NameStep",
  TypeDecl.plain "TptpIncludeInput:Outcome"]

def supportTerms : List GrammarRule := [
  ctor "tptp-include-input:decode-name" "TptpIncludeInput:NameStep"
    [("source", "Tptp92Ast:name")] (some .rewrite),
  ctor "tptp-include-input:decoded-name" "TptpIncludeInput:NameStep"
    [("name", "String")],
  ctor "tptp-include-input:classify" "TptpIncludeInput:Outcome"
    [("source-id", "String"), ("source-digest", "String"),
      ("input-index", "Integer"),
      ("path", "TptpIncludeResult:IncludeEdges"),
      ("input", "Tptp92Ast:tptp-input")] (some .rewrite),
  ctor "tptp-include-input:inspect-formula" "TptpIncludeInput:Outcome"
    [("origin", "TptpIncludeResult:FormulaOrigin"),
      ("input", "Tptp92Ast:tptp-input")] (some .rewrite),
  ctor "tptp-include-input:decode-formula" "TptpIncludeInput:Outcome"
    [("origin", "TptpIncludeResult:FormulaOrigin"),
      ("source-name", "Tptp92Ast:name"),
      ("input", "Tptp92Ast:tptp-input")] (some .rewrite),
  ctor "tptp-include-input:formula" "TptpIncludeInput:Outcome"
    [("formula", "TptpIncludeResult:ResolvedFormula")],
  ctor "tptp-include-input:include" "TptpIncludeInput:Outcome"
    [("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span")]]

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend Carrier.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists supportTypes supportTerms
    (some "TptpOfficialIncludeInputClassificationV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def language : LanguageDef := {
  name := "TptpOfficialIncludeInputClassificationV1"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem typeNames_exact :
    language.typeNames = Carrier.language.typeNames ++
      supportTypes.map (·.name) := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists,
    LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures Carrier.language ++
      supportTerms.map fun declaration =>
        (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists]

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

theorem rewrite_count : rewrites.length = 13 := by
  decide +kernel

private theorem support_type_names_nodup :
    (supportTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem support_type_names_disjoint :
    List.Disjoint signatureBase.typeNames (supportTypes.map (·.name)) := by
  have baseSeparate :
      signatureBase.typeNames.all
        (fun name => !(name.startsWith "TptpIncludeInput:")) = true := by
    decide +kernel
  have supportNamespaced :
      (supportTypes.map (·.name)).all
        (fun name => name.startsWith "TptpIncludeInput:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro name baseMembership supportMembership
  have baseNot :=
    (List.all_eq_true.mp baseSeparate) name baseMembership
  have supportYes :=
    (List.all_eq_true.mp supportNamespaced) name supportMembership
  simp [supportYes] at baseNot

private theorem support_term_labels_nodup :
    (supportTerms.map (·.label)).Nodup := by
  decide +kernel

private theorem support_term_labels_disjoint :
    List.Disjoint (signatureBase.terms.map (·.label))
      (supportTerms.map (·.label)) := by
  have baseSeparate :
      (signatureBase.terms.map (·.label)).all
        (fun label => !(label.startsWith "tptp-include-input:")) = true := by
    decide +kernel
  have supportNamespaced :
      (supportTerms.map (·.label)).all
        (fun label => label.startsWith "tptp-include-input:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label baseMembership supportMembership
  have baseNot :=
    (List.all_eq_true.mp baseSeparate) label baseMembership
  have supportYes :=
    (List.all_eq_true.mp supportNamespaced) label supportMembership
  simp [supportYes] at baseNot

private theorem support_terms_validate_all :
    supportTerms.all
      (fun term => signatureLanguage.validateTerm term == []) = true := by
  decide +kernel

private theorem support_terms_valid (term : GrammarRule)
    (membership : term ∈ supportTerms) :
    signatureLanguage.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp support_terms_validate_all) term membership
  simpa using checked

theorem signatureLanguage_validate : signatureLanguage.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    signatureBase supportTypes supportTerms
      (some "TptpOfficialIncludeInputClassificationV1")
  · simpa [signatureBase] using
      TptpOfficialIncludeResolutionResultCarrier.language_validate
  · rfl
  · rfl
  · exact support_type_names_nodup
  · exact support_type_names_disjoint
  · exact support_term_labels_nodup
  · exact support_term_labels_disjoint
  · exact support_terms_valid

private def requiredTypes : List String := [
  "String", "Integer",
  "Tptp92Ast:name", "Tptp92Ast:formula-role",
  "Tptp92Ast:annotations", "Tptp92Ast:source-span",
  "Tptp92Ast:include", "Tptp92Ast:tptp-input",
  "Tptp92Ast:annotated-formula",
  "Tptp92Ast:thf-formula", "Tptp92Ast:tff-formula",
  "Tptp92Ast:tcf-formula", "Tptp92Ast:fof-formula",
  "Tptp92Ast:cnf-formula", "Tptp92Ast:tpi-formula",
  "TptpIncludeResult:IncludeEdges",
  "TptpIncludeResult:FormulaOrigin",
  "TptpIncludeResult:ResolvedFormula",
  "TptpIncludeInput:NameStep", "TptpIncludeInput:Outcome"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) =
      true := by
  decide +kernel

private theorem requiredType_declared (name : String)
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredTypes_declared name membership)

private def requiredSignatures : List (String × Nat) := [
  ("tptp92-ast:name:alt-1", 1),
  ("tptp92-ast:name:alt-2", 1),
  ("tptp92-ast:atomic-word:alt-1", 1),
  ("tptp92-ast:atomic-word:alt-2", 1),
  ("tptp92-ast:atomic-word:alt-3", 1),
  ("tptp92-ast:token:lower-word", 1),
  ("tptp92-ast:token:single-quoted", 1),
  ("tptp92-ast:token:back-quoted", 1),
  ("tptp92-ast:token:integer", 1),
  ("tptp92-ast:tptp-input:alt-1", 2),
  ("tptp92-ast:tptp-input:alt-2", 2),
  ("tptp92-ast:source-span", 2),
  ("tptp92-ast:annotated-formula:alt-1", 1),
  ("tptp92-ast:annotated-formula:alt-2", 1),
  ("tptp92-ast:annotated-formula:alt-3", 1),
  ("tptp92-ast:annotated-formula:alt-4", 1),
  ("tptp92-ast:annotated-formula:alt-5", 1),
  ("tptp92-ast:annotated-formula:alt-6", 1),
  ("tptp92-ast:thf-annotated:alt-1", 4),
  ("tptp92-ast:tff-annotated:alt-1", 4),
  ("tptp92-ast:tcf-annotated:alt-1", 4),
  ("tptp92-ast:fof-annotated:alt-1", 4),
  ("tptp92-ast:cnf-annotated:alt-1", 4),
  ("tptp92-ast:tpi-annotated:alt-1", 4),
  ("tptp-include-result:formula-origin", 4),
  ("tptp-include-result:resolved-formula", 3),
  ("tptp-include-input:decode-name", 1),
  ("tptp-include-input:decoded-name", 1),
  ("tptp-include-input:classify", 5),
  ("tptp-include-input:inspect-formula", 2),
  ("tptp-include-input:decode-formula", 3),
  ("tptp-include-input:formula", 1),
  ("tptp-include-input:include", 2)]

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
    simpa using List.all_eq_true.mp fvarsChecked name nameMembership
  · intro name nameMembership
    apply plainName_not_constructor name
    simpa using List.all_eq_true.mp bindersChecked name nameMembership
  · intro entry entryMembership
    apply plainName_not_constructor entry.1
    simpa using List.all_eq_true.mp contextNamesChecked entry entryMembership
  · intro name nameMembership
    exact decide_eq_true_eq.mp
      (List.all_eq_true.mp rightBoundedChecked name nameMembership)

local macro "certify_classification_rows" : tactic =>
  `(tactic|
    simp [subsetCheck, contextSubsetCheck, patternSubsetCheck,
      premisesSubsetCheck, fvarsPlainCheck, bindersPlainCheck,
      contextNamesPlainCheck, nameRules, inspectFormulaRules,
      classifyFormulaRule, includeRule, finalizeFormulaRule,
      nameWordRule, nameIntegerRule, inspectFormulaRule, annotatedFormula,
      locatedFormulaInput, sourceSpan, sourceNameWord, sourceIntegerName,
      sourceAtomicWord, sourceToken, formulaOutcome, includeOutcome,
      formulaOrigin, resolvedFormula, classify, inspectFormula, decodeFormula,
      decodeName, decodedName,
      mkRule, congruence, typed, a, v,
      LanguageDef.premisePatterns, LanguageDef.patternFvarNames,
      LanguageDef.patternBinderNames, Pattern.constructorRefs,
      Pattern.constructorRefsList, Pattern.freeFvarNames,
      Pattern.isWellScoped, Pattern.isWellScopedAt,
      Pattern.isWellScopedListAt, LanguageDef.premiseFvarNames,
      LanguageDef.premiseForAllParams,
      LanguageDef.premiseProducedFvarNames, TypeExpr.baseNames,
      Pattern.zipHead, Pattern.mapHead, Pattern.evalHead, requiredTypes,
      requiredSignatures, constructorLabelReserved,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.rightBoundCheck])

private theorem name_rows_subset_checked :
    nameRules.all subsetCheck = true := by
  certify_classification_rows

private theorem classification_rows_subset_checked :
    [classifyFormulaRule, includeRule].all subsetCheck = true := by
  certify_classification_rows

private theorem inspection_rows_subset_checked :
    inspectFormulaRules.all subsetCheck = true := by
  certify_classification_rows

private theorem finalize_row_subset_checked :
    subsetCheck finalizeFormulaRule = true := by
  certify_classification_rows

private theorem every_rewrite_subset_checked :
    rewrites.all subsetCheck = true := by
  simp only [rewrites, List.all_append]
  rw [name_rows_subset_checked, classification_rows_subset_checked,
    inspection_rows_subset_checked]
  simp [finalize_row_subset_checked]

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
    CanonicalWire.languageSupported Carrier.language :=
  TptpOfficialIncludeResolutionResultCarrier.language_supported

private theorem language_terms :
    language.terms = Carrier.language.terms ++ supportTerms := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists]

private theorem terms_supported :
    language.terms.all CanonicalWire.grammarRuleSupported = true := by
  have source := base_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at source
  rw [language_terms, List.all_append, Bool.and_eq_true]
  exact ⟨source.1.2, by decide +kernel⟩

private theorem rewrites_supported :
    language.rewrites.all CanonicalWire.rewriteSupported = true := by
  decide +kernel

theorem language_supported : CanonicalWire.languageSupported language := by
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, terms_supported⟩, rewrites_supported⟩

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms rewrite_count
#print axioms language_validate
#print axioms language_supported

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeInputClassificationLanguageDef
