import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionCarrier
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-!
# Typed results for official TPTP include resolution

The source-environment carrier fixes the input boundary of include resolution.
This module fixes its complete observable output: resolved official formulae,
include-edge provenance, and every explicit resolution failure.  The carrier is
inert.  It neither reads files nor executes the resolver.

The host codec is exact for all `resolve?` results.  Typed admission additionally
checks the embedded official TPTP input, include-directive, and source-span
values.  Formula order, duplicate occurrences, and edge order remain data and
are not normalized by the carrier.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionResultCarrier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

private def ctor (label category : String)
    (parameters : List (String × String)) : GrammarRule := {
  label
  category
  params := parameters.map fun parameter =>
    .simple parameter.1 (.base parameter.2)
  syntaxPattern := []
}

def addedTypes : List TypeDecl := [
  TypeDecl.plain "TptpIncludeResult:Strings",
  TypeDecl.plain "TptpIncludeResult:FormulaSelection",
  TypeDecl.plain "TptpIncludeResult:OptionalString",
  TypeDecl.plain "TptpIncludeResult:IncludeEdge",
  TypeDecl.plain "TptpIncludeResult:IncludeEdges",
  TypeDecl.plain "TptpIncludeResult:FormulaOrigin",
  TypeDecl.plain "TptpIncludeResult:ResolvedFormula",
  TypeDecl.plain "TptpIncludeResult:ResolvedFormulas",
  TypeDecl.plain "TptpIncludeResult:ResolvedDocument",
  TypeDecl.plain "TptpIncludeResult:ResolutionError",
  TypeDecl.plain "TptpIncludeResult:ResolutionResult"]

def addedTerms : List GrammarRule := [
  ctor "tptp-include-result:strings-nil"
    "TptpIncludeResult:Strings" [],
  ctor "tptp-include-result:strings-cons"
    "TptpIncludeResult:Strings"
    [("head", "String"), ("tail", "TptpIncludeResult:Strings")],

  ctor "tptp-include-result:selection-implicit-all"
    "TptpIncludeResult:FormulaSelection" [],
  ctor "tptp-include-result:selection-explicit-all"
    "TptpIncludeResult:FormulaSelection" [],
  ctor "tptp-include-result:selection-named"
    "TptpIncludeResult:FormulaSelection"
    [("names", "TptpIncludeResult:Strings")],

  ctor "tptp-include-result:no-string"
    "TptpIncludeResult:OptionalString" [],
  ctor "tptp-include-result:some-string"
    "TptpIncludeResult:OptionalString" [("value", "String")],

  ctor "tptp-include-result:include-edge"
    "TptpIncludeResult:IncludeEdge"
    [("from-source", "String"), ("from-input-index", "Integer"),
      ("requested-file", "String"), ("target-source", "String"),
      ("target-digest", "String"),
      ("selection", "TptpIncludeResult:FormulaSelection"),
      ("space-name", "TptpIncludeResult:OptionalString"),
      ("directive", "Tptp92Ast:include"),
      ("span", "Tptp92Ast:source-span")],
  ctor "tptp-include-result:include-edges-nil"
    "TptpIncludeResult:IncludeEdges" [],
  ctor "tptp-include-result:include-edges-cons"
    "TptpIncludeResult:IncludeEdges"
    [("head", "TptpIncludeResult:IncludeEdge"),
      ("tail", "TptpIncludeResult:IncludeEdges")],

  ctor "tptp-include-result:formula-origin"
    "TptpIncludeResult:FormulaOrigin"
    [("source-id", "String"), ("source-digest", "String"),
      ("source-input-index", "Integer"),
      ("include-path", "TptpIncludeResult:IncludeEdges")],
  ctor "tptp-include-result:resolved-formula"
    "TptpIncludeResult:ResolvedFormula"
    [("name", "String"), ("input", "Tptp92Ast:tptp-input"),
      ("origin", "TptpIncludeResult:FormulaOrigin")],
  ctor "tptp-include-result:resolved-formulas-nil"
    "TptpIncludeResult:ResolvedFormulas" [],
  ctor "tptp-include-result:resolved-formulas-cons"
    "TptpIncludeResult:ResolvedFormulas"
    [("head", "TptpIncludeResult:ResolvedFormula"),
      ("tail", "TptpIncludeResult:ResolvedFormulas")],
  ctor "tptp-include-result:resolved-document"
    "TptpIncludeResult:ResolvedDocument"
    [("root-source", "String"), ("root-digest", "String"),
      ("formulas", "TptpIncludeResult:ResolvedFormulas"),
      ("edges", "TptpIncludeResult:IncludeEdges")],

  ctor "tptp-include-result:error-missing-document"
    "TptpIncludeResult:ResolutionError" [("canonical-id", "String")],
  ctor "tptp-include-result:error-ambiguous-document"
    "TptpIncludeResult:ResolutionError" [("canonical-id", "String")],
  ctor "tptp-include-result:error-missing-binding"
    "TptpIncludeResult:ResolutionError"
    [("from-source", "String"), ("requested-file", "String")],
  ctor "tptp-include-result:error-ambiguous-binding"
    "TptpIncludeResult:ResolutionError"
    [("from-source", "String"), ("requested-file", "String")],
  ctor "tptp-include-result:error-malformed-document"
    "TptpIncludeResult:ResolutionError" [("canonical-id", "String")],
  ctor "tptp-include-result:error-malformed-input"
    "TptpIncludeResult:ResolutionError"
    [("canonical-id", "String"), ("input-index", "Integer")],
  ctor "tptp-include-result:error-malformed-formula"
    "TptpIncludeResult:ResolutionError"
    [("canonical-id", "String"), ("input-index", "Integer")],
  ctor "tptp-include-result:error-malformed-include"
    "TptpIncludeResult:ResolutionError"
    [("canonical-id", "String"), ("input-index", "Integer")],
  ctor "tptp-include-result:error-duplicate-selection-name"
    "TptpIncludeResult:ResolutionError"
    [("target-source", "String"), ("name", "String")],
  ctor "tptp-include-result:error-missing-selection-name"
    "TptpIncludeResult:ResolutionError"
    [("target-source", "String"), ("name", "String")],
  ctor "tptp-include-result:error-ambiguous-selection-name"
    "TptpIncludeResult:ResolutionError"
    [("target-source", "String"), ("name", "String")],
  ctor "tptp-include-result:error-unsupported-space-namespace"
    "TptpIncludeResult:ResolutionError"
    [("from-source", "String"), ("requested-file", "String"),
      ("space-name", "String")],
  ctor "tptp-include-result:error-cycle"
    "TptpIncludeResult:ResolutionError"
    [("canonical-path", "TptpIncludeResult:Strings")],
  ctor "tptp-include-result:error-source-depth-exhausted"
    "TptpIncludeResult:ResolutionError"
    [("canonical-path", "TptpIncludeResult:Strings")],
  ctor "tptp-include-result:error-refinement-rejected"
    "TptpIncludeResult:ResolutionError"
    [("root-source", "String"), ("resolution-digest", "String")],

  ctor "tptp-include-result:resolution-error"
    "TptpIncludeResult:ResolutionResult"
    [("error", "TptpIncludeResult:ResolutionError")],
  ctor "tptp-include-result:resolution-ok"
    "TptpIncludeResult:ResolutionResult"
    [("document", "TptpIncludeResult:ResolvedDocument")]]

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpOfficialIncludeResolutionCarrier.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeResolutionResultCarrierV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def language : LanguageDef := signatureCalculusLanguage.toLanguageDef

@[simp] theorem typeNames_exact :
    language.typeNames = TptpOfficialIncludeResolutionCarrier.language.typeNames ++
      addedTypes.map (·.name) := by
  simp [language, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists,
    LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpOfficialIncludeResolutionCarrier.language ++
      addedTerms.map fun declaration =>
        (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureCalculusLanguage, signatureExtension, signatureBase,
    ConstructorSignatureExtension.ofLists]

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.toLanguageDef.typeNames
      (addedTypes.map (·.name)) := by
  have baseSeparate :
      signatureBase.toLanguageDef.typeNames.all
        (fun name => !(name.startsWith "TptpIncludeResult:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTypes.map (·.name)).all
        (fun name => name.startsWith "TptpIncludeResult:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro name baseMembership addedMembership
  have baseNot :=
    (List.all_eq_true.mp baseSeparate) name baseMembership
  have addedYes :=
    (List.all_eq_true.mp addedNamespaced) name addedMembership
  simp [addedYes] at baseNot

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.terms.map (·.label))
      (addedTerms.map (·.label)) := by
  have baseSeparate :
      (signatureBase.terms.map (·.label)).all
        (fun label => !(label.startsWith "tptp-include-result:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTerms.map (·.label)).all
        (fun label => label.startsWith "tptp-include-result:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label baseMembership addedMembership
  have baseNot :=
    (List.all_eq_true.mp baseSeparate) label baseMembership
  have addedYes :=
    (List.all_eq_true.mp addedNamespaced) label addedMembership
  simp [addedYes] at baseNot

private theorem added_terms_validate_all :
    addedTerms.all (fun term => language.validateTerm term == []) = true := by
  decide +kernel

private theorem added_terms_valid (term : GrammarRule)
    (membership : term ∈ addedTerms) :
    language.validateTerm term = [] := by
  have checked :=
    (List.all_eq_true.mp added_terms_validate_all) term membership
  simpa using checked

theorem language_validate : language.validate = [] := by
  apply ConstructorSignatureExtension.apply_language_validate
    signatureBase addedTypes addedTerms
      (some "TptpOfficialIncludeResolutionResultCarrierV1")
  · simpa [signatureBase] using
      TptpOfficialIncludeResolutionCarrier.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

private theorem language_terms :
    language.terms =
      TptpOfficialIncludeResolutionCarrier.language.terms ++ addedTerms := by
  simp [language, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists]

private theorem source_supported :
    CanonicalWire.languageSupported
      TptpOfficialIncludeResolutionCarrier.language := by
  exact TptpOfficialIncludeResolutionCarrier.language_supported

private theorem terms_supported :
    language.terms.all CanonicalWire.grammarRuleSupported = true := by
  have source := source_supported
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true] at source
  rw [language_terms, List.all_append]
  simp [source.1.2, addedTerms, ctor, CanonicalWire.grammarRuleSupported,
    CanonicalWire.termParamSupported, CanonicalWire.typeExprSupported]

theorem language_supported : CanonicalWire.languageSupported language := by
  simp only [CanonicalWire.languageSupported, Bool.and_eq_true]
  exact ⟨⟨rfl, terms_supported⟩, rfl⟩

def wire : String :=
  (CanonicalWire.renderLanguage? language).getD ""

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

/-! ## Exact host codec -/

abbrev encodeString := TptpOfficialIncludeResolutionCarrier.encodeString
abbrev decodeString? := TptpOfficialIncludeResolutionCarrier.decodeString?

def encodeIndex (index : Nat) : Pattern := a (toString index)

def decodeIndex? : Pattern -> Option Nat
  | .apply value [] => value.toNat?
  | _ => none

def encodeStrings : List String -> Pattern
  | [] => a "tptp-include-result:strings-nil"
  | value :: values =>
      a "tptp-include-result:strings-cons"
        [encodeString value, encodeStrings values]

def decodeStrings? : Pattern -> Option (List String)
  | .apply "tptp-include-result:strings-nil" [] => some []
  | .apply "tptp-include-result:strings-cons" [value, values] => do
      let value <- decodeString? value
      let values <- decodeStrings? values
      some (value :: values)
  | _ => none

def encodeFormulaSelection : FormulaSelection -> Pattern
  | .implicitAll => a "tptp-include-result:selection-implicit-all"
  | .explicitAll => a "tptp-include-result:selection-explicit-all"
  | .named names =>
      a "tptp-include-result:selection-named" [encodeStrings names]

def decodeFormulaSelection? : Pattern -> Option FormulaSelection
  | .apply "tptp-include-result:selection-implicit-all" [] =>
      some .implicitAll
  | .apply "tptp-include-result:selection-explicit-all" [] =>
      some .explicitAll
  | .apply "tptp-include-result:selection-named" [names] => do
      let names <- decodeStrings? names
      some (.named names)
  | _ => none

def encodeOptionalString : Option String -> Pattern
  | none => a "tptp-include-result:no-string"
  | some value => a "tptp-include-result:some-string" [encodeString value]

def decodeOptionalString? : Pattern -> Option (Option String)
  | .apply "tptp-include-result:no-string" [] => some none
  | .apply "tptp-include-result:some-string" [value] => do
      let value <- decodeString? value
      some (some value)
  | _ => none

def encodeIncludeEdge (edge : IncludeEdge) : Pattern :=
  a "tptp-include-result:include-edge"
    [encodeString edge.fromSource, encodeIndex edge.fromInputIndex,
      encodeString edge.requestedFile, encodeString edge.targetSource,
      encodeString edge.targetDigest, encodeFormulaSelection edge.selection,
      encodeOptionalString edge.spaceName, edge.directive, edge.span]

def decodeIncludeEdge? : Pattern -> Option IncludeEdge
  | .apply "tptp-include-result:include-edge"
      [fromSource, fromInputIndex, requestedFile, targetSource,
        targetDigest, selection, spaceName, directive, span] => do
      let fromSource <- decodeString? fromSource
      let fromInputIndex <- decodeIndex? fromInputIndex
      let requestedFile <- decodeString? requestedFile
      let targetSource <- decodeString? targetSource
      let targetDigest <- decodeString? targetDigest
      let selection <- decodeFormulaSelection? selection
      let spaceName <- decodeOptionalString? spaceName
      some ({
        fromSource := fromSource
        fromInputIndex := fromInputIndex
        requestedFile := requestedFile
        targetSource := targetSource
        targetDigest := targetDigest
        selection := selection
        spaceName := spaceName
        directive := directive
        span := span
      } : IncludeEdge)
  | _ => none

def encodeIncludeEdges : List IncludeEdge -> Pattern
  | [] => a "tptp-include-result:include-edges-nil"
  | edge :: edges =>
      a "tptp-include-result:include-edges-cons"
        [encodeIncludeEdge edge, encodeIncludeEdges edges]

def decodeIncludeEdges? : Pattern -> Option (List IncludeEdge)
  | .apply "tptp-include-result:include-edges-nil" [] => some []
  | .apply "tptp-include-result:include-edges-cons" [edge, edges] => do
      let edge <- decodeIncludeEdge? edge
      let edges <- decodeIncludeEdges? edges
      some (edge :: edges)
  | _ => none

def encodeFormulaOrigin (origin : FormulaOrigin) : Pattern :=
  a "tptp-include-result:formula-origin"
    [encodeString origin.sourceId, encodeString origin.sourceDigest,
      encodeIndex origin.sourceInputIndex,
      encodeIncludeEdges origin.includePath]

def decodeFormulaOrigin? : Pattern -> Option FormulaOrigin
  | .apply "tptp-include-result:formula-origin"
      [sourceId, sourceDigest, sourceInputIndex, includePath] => do
      let sourceId <- decodeString? sourceId
      let sourceDigest <- decodeString? sourceDigest
      let sourceInputIndex <- decodeIndex? sourceInputIndex
      let includePath <- decodeIncludeEdges? includePath
      some { sourceId, sourceDigest, sourceInputIndex, includePath }
  | _ => none

def encodeResolvedFormula (formula : ResolvedFormula) : Pattern :=
  a "tptp-include-result:resolved-formula"
    [encodeString formula.name, formula.input,
      encodeFormulaOrigin formula.origin]

def decodeResolvedFormula? : Pattern -> Option ResolvedFormula
  | .apply "tptp-include-result:resolved-formula" [name, input, origin] => do
      let name <- decodeString? name
      let origin <- decodeFormulaOrigin? origin
      some { name, input, origin }
  | _ => none

def encodeResolvedFormulas : List ResolvedFormula -> Pattern
  | [] => a "tptp-include-result:resolved-formulas-nil"
  | formula :: formulas =>
      a "tptp-include-result:resolved-formulas-cons"
        [encodeResolvedFormula formula, encodeResolvedFormulas formulas]

def decodeResolvedFormulas? : Pattern -> Option (List ResolvedFormula)
  | .apply "tptp-include-result:resolved-formulas-nil" [] => some []
  | .apply "tptp-include-result:resolved-formulas-cons"
      [formula, formulas] => do
      let formula <- decodeResolvedFormula? formula
      let formulas <- decodeResolvedFormulas? formulas
      some (formula :: formulas)
  | _ => none

def encodeResolvedDocument (resolved : ResolvedDocument) : Pattern :=
  a "tptp-include-result:resolved-document"
    [encodeString resolved.rootSource, encodeString resolved.rootDigest,
      encodeResolvedFormulas resolved.formulas,
      encodeIncludeEdges resolved.edges]

def decodeResolvedDocument? : Pattern -> Option ResolvedDocument
  | .apply "tptp-include-result:resolved-document"
      [rootSource, rootDigest, formulas, edges] => do
      let rootSource <- decodeString? rootSource
      let rootDigest <- decodeString? rootDigest
      let formulas <- decodeResolvedFormulas? formulas
      let edges <- decodeIncludeEdges? edges
      some { rootSource, rootDigest, formulas, edges }
  | _ => none

def encodeResolutionError : ResolutionError -> Pattern
  | .missingDocument canonicalId =>
      a "tptp-include-result:error-missing-document"
        [encodeString canonicalId]
  | .ambiguousDocument canonicalId =>
      a "tptp-include-result:error-ambiguous-document"
        [encodeString canonicalId]
  | .missingBinding fromSource requestedFile =>
      a "tptp-include-result:error-missing-binding"
        [encodeString fromSource, encodeString requestedFile]
  | .ambiguousBinding fromSource requestedFile =>
      a "tptp-include-result:error-ambiguous-binding"
        [encodeString fromSource, encodeString requestedFile]
  | .malformedDocument canonicalId =>
      a "tptp-include-result:error-malformed-document"
        [encodeString canonicalId]
  | .malformedInput canonicalId inputIndex =>
      a "tptp-include-result:error-malformed-input"
        [encodeString canonicalId, encodeIndex inputIndex]
  | .malformedFormula canonicalId inputIndex =>
      a "tptp-include-result:error-malformed-formula"
        [encodeString canonicalId, encodeIndex inputIndex]
  | .malformedInclude canonicalId inputIndex =>
      a "tptp-include-result:error-malformed-include"
        [encodeString canonicalId, encodeIndex inputIndex]
  | .duplicateSelectionName targetSource name =>
      a "tptp-include-result:error-duplicate-selection-name"
        [encodeString targetSource, encodeString name]
  | .missingSelectionName targetSource name =>
      a "tptp-include-result:error-missing-selection-name"
        [encodeString targetSource, encodeString name]
  | .ambiguousSelectionName targetSource name =>
      a "tptp-include-result:error-ambiguous-selection-name"
        [encodeString targetSource, encodeString name]
  | .unsupportedSpaceNamespace fromSource requestedFile spaceName =>
      a "tptp-include-result:error-unsupported-space-namespace"
        [encodeString fromSource, encodeString requestedFile,
          encodeString spaceName]
  | .cycle canonicalPath =>
      a "tptp-include-result:error-cycle" [encodeStrings canonicalPath]
  | .sourceDepthExhausted canonicalPath =>
      a "tptp-include-result:error-source-depth-exhausted"
        [encodeStrings canonicalPath]
  | .refinementRejected rootSource resolutionDigest =>
      a "tptp-include-result:error-refinement-rejected"
        [encodeString rootSource, encodeString resolutionDigest]

def decodeResolutionError? : Pattern -> Option ResolutionError
  | .apply "tptp-include-result:error-missing-document" [canonicalId] => do
      let canonicalId <- decodeString? canonicalId
      some (.missingDocument canonicalId)
  | .apply "tptp-include-result:error-ambiguous-document" [canonicalId] => do
      let canonicalId <- decodeString? canonicalId
      some (.ambiguousDocument canonicalId)
  | .apply "tptp-include-result:error-missing-binding"
      [fromSource, requestedFile] => do
      let fromSource <- decodeString? fromSource
      let requestedFile <- decodeString? requestedFile
      some (.missingBinding fromSource requestedFile)
  | .apply "tptp-include-result:error-ambiguous-binding"
      [fromSource, requestedFile] => do
      let fromSource <- decodeString? fromSource
      let requestedFile <- decodeString? requestedFile
      some (.ambiguousBinding fromSource requestedFile)
  | .apply "tptp-include-result:error-malformed-document" [canonicalId] => do
      let canonicalId <- decodeString? canonicalId
      some (.malformedDocument canonicalId)
  | .apply "tptp-include-result:error-malformed-input"
      [canonicalId, inputIndex] => do
      let canonicalId <- decodeString? canonicalId
      let inputIndex <- decodeIndex? inputIndex
      some (.malformedInput canonicalId inputIndex)
  | .apply "tptp-include-result:error-malformed-formula"
      [canonicalId, inputIndex] => do
      let canonicalId <- decodeString? canonicalId
      let inputIndex <- decodeIndex? inputIndex
      some (.malformedFormula canonicalId inputIndex)
  | .apply "tptp-include-result:error-malformed-include"
      [canonicalId, inputIndex] => do
      let canonicalId <- decodeString? canonicalId
      let inputIndex <- decodeIndex? inputIndex
      some (.malformedInclude canonicalId inputIndex)
  | .apply "tptp-include-result:error-duplicate-selection-name"
      [targetSource, name] => do
      let targetSource <- decodeString? targetSource
      let name <- decodeString? name
      some (.duplicateSelectionName targetSource name)
  | .apply "tptp-include-result:error-missing-selection-name"
      [targetSource, name] => do
      let targetSource <- decodeString? targetSource
      let name <- decodeString? name
      some (.missingSelectionName targetSource name)
  | .apply "tptp-include-result:error-ambiguous-selection-name"
      [targetSource, name] => do
      let targetSource <- decodeString? targetSource
      let name <- decodeString? name
      some (.ambiguousSelectionName targetSource name)
  | .apply "tptp-include-result:error-unsupported-space-namespace"
      [fromSource, requestedFile, spaceName] => do
      let fromSource <- decodeString? fromSource
      let requestedFile <- decodeString? requestedFile
      let spaceName <- decodeString? spaceName
      some (.unsupportedSpaceNamespace fromSource requestedFile spaceName)
  | .apply "tptp-include-result:error-cycle" [canonicalPath] => do
      let canonicalPath <- decodeStrings? canonicalPath
      some (.cycle canonicalPath)
  | .apply "tptp-include-result:error-source-depth-exhausted"
      [canonicalPath] => do
      let canonicalPath <- decodeStrings? canonicalPath
      some (.sourceDepthExhausted canonicalPath)
  | .apply "tptp-include-result:error-refinement-rejected"
      [rootSource, resolutionDigest] => do
      let rootSource <- decodeString? rootSource
      let resolutionDigest <- decodeString? resolutionDigest
      some (.refinementRejected rootSource resolutionDigest)
  | _ => none

def encodeResolutionResult :
    Except ResolutionError ResolvedDocument -> Pattern
  | .error failure =>
      a "tptp-include-result:resolution-error"
        [encodeResolutionError failure]
  | .ok resolved =>
      a "tptp-include-result:resolution-ok"
        [encodeResolvedDocument resolved]

def decodeResolutionResult? :
    Pattern -> Option (Except ResolutionError ResolvedDocument)
  | .apply "tptp-include-result:resolution-error" [failure] => do
      let failure <- decodeResolutionError? failure
      some (.error failure)
  | .apply "tptp-include-result:resolution-ok" [resolved] => do
      let resolved <- decodeResolvedDocument? resolved
      some (.ok resolved)
  | _ => none

@[simp] theorem decodeIndex_encodeIndex (index : Nat) :
    decodeIndex? (encodeIndex index) = some index := by
  simp [decodeIndex?, encodeIndex, a, Nat.toNat?_repr]

@[simp] theorem decodeStrings_encodeStrings (values : List String) :
    decodeStrings? (encodeStrings values) = some values := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [encodeStrings, decodeStrings?, a, inductionHypothesis,
        TptpOfficialIncludeResolutionCarrier.decodeString_encodeString]

@[simp] theorem decodeFormulaSelection_encodeFormulaSelection
    (selection : FormulaSelection) :
    decodeFormulaSelection? (encodeFormulaSelection selection) =
      some selection := by
  cases selection <;>
    simp [encodeFormulaSelection, decodeFormulaSelection?, a]

@[simp] theorem decodeOptionalString_encodeOptionalString
    (value : Option String) :
    decodeOptionalString? (encodeOptionalString value) = some value := by
  cases value <;>
    simp [encodeOptionalString, decodeOptionalString?, a,
      TptpOfficialIncludeResolutionCarrier.decodeString_encodeString]

@[simp] theorem decodeIncludeEdge_encodeIncludeEdge (edge : IncludeEdge) :
    decodeIncludeEdge? (encodeIncludeEdge edge) = some edge := by
  cases edge
  simp [encodeIncludeEdge, decodeIncludeEdge?, a,
    TptpOfficialIncludeResolutionCarrier.decodeString_encodeString]

@[simp] theorem decodeIncludeEdges_encodeIncludeEdges
    (edges : List IncludeEdge) :
    decodeIncludeEdges? (encodeIncludeEdges edges) = some edges := by
  induction edges with
  | nil => rfl
  | cons edge edges inductionHypothesis =>
      simp [encodeIncludeEdges, decodeIncludeEdges?, a, inductionHypothesis]

@[simp] theorem decodeFormulaOrigin_encodeFormulaOrigin
    (origin : FormulaOrigin) :
    decodeFormulaOrigin? (encodeFormulaOrigin origin) = some origin := by
  cases origin
  simp [encodeFormulaOrigin, decodeFormulaOrigin?, a,
    TptpOfficialIncludeResolutionCarrier.decodeString_encodeString]

@[simp] theorem decodeResolvedFormula_encodeResolvedFormula
    (formula : ResolvedFormula) :
    decodeResolvedFormula? (encodeResolvedFormula formula) = some formula := by
  cases formula
  simp [encodeResolvedFormula, decodeResolvedFormula?, a,
    TptpOfficialIncludeResolutionCarrier.decodeString_encodeString]

@[simp] theorem decodeResolvedFormulas_encodeResolvedFormulas
    (formulas : List ResolvedFormula) :
    decodeResolvedFormulas? (encodeResolvedFormulas formulas) =
      some formulas := by
  induction formulas with
  | nil => rfl
  | cons formula formulas inductionHypothesis =>
      simp [encodeResolvedFormulas, decodeResolvedFormulas?, a,
        inductionHypothesis]

@[simp] theorem decodeResolvedDocument_encodeResolvedDocument
    (resolved : ResolvedDocument) :
    decodeResolvedDocument? (encodeResolvedDocument resolved) =
      some resolved := by
  cases resolved
  simp [encodeResolvedDocument, decodeResolvedDocument?, a,
    TptpOfficialIncludeResolutionCarrier.decodeString_encodeString]

@[simp] theorem decodeResolutionError_encodeResolutionError
    (failure : ResolutionError) :
    decodeResolutionError? (encodeResolutionError failure) = some failure := by
  cases failure <;>
    simp [encodeResolutionError, decodeResolutionError?, a,
      TptpOfficialIncludeResolutionCarrier.decodeString_encodeString]

@[simp] theorem decodeResolutionResult_encodeResolutionResult
    (result : Except ResolutionError ResolvedDocument) :
    decodeResolutionResult? (encodeResolutionResult result) = some result := by
  cases result <;>
    simp [encodeResolutionResult, decodeResolutionResult?, a]

theorem encodeResolutionResult_injective :
    Function.Injective encodeResolutionResult := by
  intro first second equalEncoding
  have decoded := congrArg decodeResolutionResult? equalEncoding
  simpa only [decodeResolutionResult_encodeResolutionResult,
    Option.some.injEq] using decoded

/-! ## Positive and adversarial controls -/

namespace Canary

def nestedResult : Except ResolutionError ResolvedDocument :=
  resolve? TptpOfficialIncludeResolution.Canary.nestedEnvironment "root"

theorem nested_result_round_trip :
    decodeResolutionResult? (encodeResolutionResult nestedResult) =
      some nestedResult := by
  exact decodeResolutionResult_encodeResolutionResult _

def admittedEdge : IncludeEdge := {
  fromSource := "root"
  fromInputIndex := 0
  requestedFile := "leaf.p"
  targetSource := "leaf"
  targetDigest := "leaf-digest"
  selection := .implicitAll
  spaceName := none
  directive := a "tptp92-ast:include:alt-1" [
    a "tptp92-ast:file-name:alt-1" [
      TptpOfficialIncludeResolution.Canary.quotedWord "leaf.p"],
    a "tptp92-ast:include-optionals:alt-1"]
  span := TptpOfficialIncludeResolution.Canary.span 0
}

def admittedResolved : ResolvedDocument := {
  rootSource := "root"
  rootDigest := "root-digest"
  formulas := []
  edges := []
}

def admittedResult : Except ResolutionError ResolvedDocument :=
  .ok admittedResolved

theorem admitted_result_inhabits_carrier :
    CarrierWellSorted.checkHasType language WellSorted.FreeTypeContext.empty []
        (encodeResolutionResult admittedResult)
        (.base "TptpIncludeResult:ResolutionResult") = true := by
  decide +kernel

def missingSelectionResult : Except ResolutionError ResolvedDocument :=
  resolve? TptpOfficialIncludeResolution.Canary.missingSelectionEnvironment
    "missing-selection-root"

theorem missing_selection_result_is_exact :
    missingSelectionResult =
      .error (.missingSelectionName "leaf" "z") := by
  rfl

theorem missing_selection_result_inhabits_carrier :
    CarrierWellSorted.checkHasType language WellSorted.FreeTypeContext.empty []
        (encodeResolutionResult missingSelectionResult)
        (.base "TptpIncludeResult:ResolutionResult") = true := by
  decide +kernel

def malformedEmbeddedInputResult : Except ResolutionError ResolvedDocument :=
  .ok {
    rootSource := "root"
    rootDigest := "root-digest"
    formulas := [{
      name := "not-official"
      input := a "not-an-official-tptp-input"
      origin := {
        sourceId := "root"
        sourceDigest := "root-digest"
        sourceInputIndex := 0
        includePath := []
      }
    }]
    edges := []
  }

theorem malformed_embedded_input_shape_round_trips :
    decodeResolutionResult?
        (encodeResolutionResult malformedEmbeddedInputResult) =
      some malformedEmbeddedInputResult := by
  exact decodeResolutionResult_encodeResolutionResult _

theorem malformed_embedded_input_does_not_inhabit_carrier :
    CarrierWellSorted.checkHasType language WellSorted.FreeTypeContext.empty []
        (encodeResolutionResult malformedEmbeddedInputResult)
        (.base "TptpIncludeResult:ResolutionResult") = false := by
  decide +kernel

theorem wrong_outer_constructor_is_rejected :
    decodeResolutionResult? (a "not-a-resolution-result") = none := by
  rfl

end Canary

#print axioms language_validate
#print axioms language_supported
#print axioms decodeResolutionResult_encodeResolutionResult
#print axioms encodeResolutionResult_injective
#print axioms Canary.nested_result_round_trip
#print axioms Canary.admitted_result_inhabits_carrier
#print axioms Canary.missing_selection_result_is_exact
#print axioms Canary.missing_selection_result_inhabits_carrier
#print axioms Canary.malformed_embedded_input_shape_round_trips
#print axioms Canary.malformed_embedded_input_does_not_inhabit_carrier
#print axioms Canary.wrong_outer_constructor_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionResultCarrier
