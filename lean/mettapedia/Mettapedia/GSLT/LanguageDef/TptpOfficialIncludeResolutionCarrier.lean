import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate

/-!
# Typed carrier for official TPTP include-resolution environments

The filesystem boundary loads and parses a finite family of TPTP sources.
The pure include resolver consumes canonical source identities, content
digests, official abstract-syntax trees, and parent-relative include bindings.
This module gives that boundary an explicit `LanguageDef` carrier.

Shape decoding and typed admission are intentionally distinct.  Shape decoding
round-trips every host `SourceEnvironment`.  Typed decoding additionally checks
that each embedded source is an official `Tptp92Ast:tptp-file`.  Duplicate
source identities and duplicate bindings remain well-formed carrier data: the
pure resolver, not the carrier, rejects those semantic ambiguities.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionCarrier

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
  TypeDecl.plain "TptpIncludeResolution:SourceDocument",
  TypeDecl.plain "TptpIncludeResolution:SourceDocuments",
  TypeDecl.plain "TptpIncludeResolution:IncludeBinding",
  TypeDecl.plain "TptpIncludeResolution:IncludeBindings",
  TypeDecl.plain "TptpIncludeResolution:SourceEnvironment"]

def addedTerms : List GrammarRule := [
  ctor "tptp-include-resolution:source-document"
    "TptpIncludeResolution:SourceDocument"
    [("canonical-id", "String"), ("digest", "String"),
      ("official-file", "Tptp92Ast:tptp-file")],
  ctor "tptp-include-resolution:source-documents-nil"
    "TptpIncludeResolution:SourceDocuments" [],
  ctor "tptp-include-resolution:source-documents-cons"
    "TptpIncludeResolution:SourceDocuments"
    [("head", "TptpIncludeResolution:SourceDocument"),
      ("tail", "TptpIncludeResolution:SourceDocuments")],
  ctor "tptp-include-resolution:include-binding"
    "TptpIncludeResolution:IncludeBinding"
    [("from-source", "String"), ("requested-file", "String"),
      ("target-source", "String")],
  ctor "tptp-include-resolution:include-bindings-nil"
    "TptpIncludeResolution:IncludeBindings" [],
  ctor "tptp-include-resolution:include-bindings-cons"
    "TptpIncludeResolution:IncludeBindings"
    [("head", "TptpIncludeResolution:IncludeBinding"),
      ("tail", "TptpIncludeResolution:IncludeBindings")],
  ctor "tptp-include-resolution:source-environment"
    "TptpIncludeResolution:SourceEnvironment"
    [("documents", "TptpIncludeResolution:SourceDocuments"),
      ("bindings", "TptpIncludeResolution:IncludeBindings")]]

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend TptpOfficialAbstractSyntax.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeResolutionCarrierV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def language : LanguageDef := signatureCalculusLanguage.toLanguageDef

@[simp] theorem typeNames_exact :
    language.typeNames = TptpOfficialAbstractSyntax.language.typeNames ++
      addedTypes.map (·.name) := by
  simp [language, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists,
    LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures
        TptpOfficialAbstractSyntax.language ++
      addedTerms.map fun declaration =>
        (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureCalculusLanguage, signatureExtension, signatureBase,
    ConstructorSignatureExtension.ofLists]

private theorem added_type_names_nodup :
    (addedTypes.map (·.name)).Nodup := by
  decide +kernel

private theorem added_type_names_disjoint :
    List.Disjoint signatureBase.typeNames (addedTypes.map (·.name)) := by
  rw [List.disjoint_left]
  intro name sourceMembership addedMembership
  simp [addedTypes] at addedMembership
  rcases addedMembership with rfl | rfl | rfl | rfl | rfl
  all_goals
    change _ ∈ TptpOfficialAbstractSyntax.language.typeNames at sourceMembership
    revert sourceMembership
    decide +kernel

private theorem added_term_labels_nodup :
    (addedTerms.map (·.label)).Nodup := by
  decide +kernel

private theorem added_term_labels_disjoint :
    List.Disjoint (signatureBase.terms.map (·.label))
      (addedTerms.map (·.label)) := by
  have sourceNamespaced :
      (signatureBase.terms.map (·.label)).all
        (fun label => label.startsWith "tptp92-ast:") = true := by
    simpa [signatureBase] using
      TptpOfficialAbstractSyntax.constructorLabels_namespaced
  have addedSeparate :
      (addedTerms.map (·.label)).all
        (fun label => !(label.startsWith "tptp92-ast:")) = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label sourceMembership addedMembership
  have sourcePrefix :=
    (List.all_eq_true.mp sourceNamespaced) label sourceMembership
  have targetNotPrefix :=
    (List.all_eq_true.mp addedSeparate) label addedMembership
  simp [sourcePrefix] at targetNotPrefix

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
      (some "TptpOfficialIncludeResolutionCarrierV1")
  · simpa [signatureBase] using TptpOfficialAbstractSyntax.language_validate
  · rfl
  · rfl
  · exact added_type_names_nodup
  · exact added_type_names_disjoint
  · exact added_term_labels_nodup
  · exact added_term_labels_disjoint
  · exact added_terms_valid

def validated : ValidatedLanguageDef := ⟨language, language_validate⟩

private theorem source_supported :
    CanonicalWire.languageSupported TptpOfficialAbstractSyntax.language := by
  rw [← CanonicalWire.renderLanguage?_isSome_eq_supported]
  exact TptpOfficialAbstractSyntax.wire_isSome

private theorem language_terms :
    language.terms = TptpOfficialAbstractSyntax.language.terms ++ addedTerms := by
  simp [language, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists]

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

/-! ## Exact host-to-carrier codec -/

def encodeString (value : String) : Pattern := a value

def decodeString? : Pattern -> Option String
  | .apply value [] => some value
  | _ => none

def encodeSourceDocument (document : SourceDocument) : Pattern :=
  a "tptp-include-resolution:source-document"
    [encodeString document.canonicalId, encodeString document.digest,
      document.officialFile]

def decodeSourceDocumentShape? : Pattern -> Option SourceDocument
  | .apply "tptp-include-resolution:source-document"
      [canonicalId, digest, officialFile] => do
      let canonicalId <- decodeString? canonicalId
      let digest <- decodeString? digest
      some { canonicalId, digest, officialFile }
  | _ => none

def encodeSourceDocuments : List SourceDocument -> Pattern
  | [] => a "tptp-include-resolution:source-documents-nil"
  | document :: documents =>
      a "tptp-include-resolution:source-documents-cons"
        [encodeSourceDocument document, encodeSourceDocuments documents]

def decodeSourceDocumentsShape? : Pattern -> Option (List SourceDocument)
  | .apply "tptp-include-resolution:source-documents-nil" [] => some []
  | .apply "tptp-include-resolution:source-documents-cons"
      [document, documents] => do
      let decodedDocument <- decodeSourceDocumentShape? document
      let decodedDocuments <- decodeSourceDocumentsShape? documents
      some (decodedDocument :: decodedDocuments)
  | _ => none

def encodeIncludeBinding (binding : IncludeBinding) : Pattern :=
  a "tptp-include-resolution:include-binding"
    [encodeString binding.fromSource, encodeString binding.requestedFile,
      encodeString binding.targetSource]

def decodeIncludeBindingShape? : Pattern -> Option IncludeBinding
  | .apply "tptp-include-resolution:include-binding"
      [fromSource, requestedFile, targetSource] => do
      let fromSource <- decodeString? fromSource
      let requestedFile <- decodeString? requestedFile
      let targetSource <- decodeString? targetSource
      some { fromSource, requestedFile, targetSource }
  | _ => none

def encodeIncludeBindings : List IncludeBinding -> Pattern
  | [] => a "tptp-include-resolution:include-bindings-nil"
  | binding :: bindings =>
      a "tptp-include-resolution:include-bindings-cons"
        [encodeIncludeBinding binding, encodeIncludeBindings bindings]

def decodeIncludeBindingsShape? : Pattern -> Option (List IncludeBinding)
  | .apply "tptp-include-resolution:include-bindings-nil" [] => some []
  | .apply "tptp-include-resolution:include-bindings-cons"
      [binding, bindings] => do
      let decodedBinding <- decodeIncludeBindingShape? binding
      let decodedBindings <- decodeIncludeBindingsShape? bindings
      some (decodedBinding :: decodedBindings)
  | _ => none

def encodeSourceEnvironment (environment : SourceEnvironment) : Pattern :=
  a "tptp-include-resolution:source-environment"
    [encodeSourceDocuments environment.documents,
      encodeIncludeBindings environment.bindings]

def decodeSourceEnvironmentShape? : Pattern -> Option SourceEnvironment
  | .apply "tptp-include-resolution:source-environment"
      [documents, bindings] => do
      let documents <- decodeSourceDocumentsShape? documents
      let bindings <- decodeIncludeBindingsShape? bindings
      some { documents, bindings }
  | _ => none

@[simp] theorem decodeString_encodeString (value : String) :
    decodeString? (encodeString value) = some value := by
  rfl

@[simp] theorem decodeSourceDocumentShape_encodeSourceDocument
    (document : SourceDocument) :
    decodeSourceDocumentShape? (encodeSourceDocument document) =
      some document := by
  cases document
  rfl

@[simp] theorem decodeSourceDocumentsShape_encodeSourceDocuments
    (documents : List SourceDocument) :
    decodeSourceDocumentsShape? (encodeSourceDocuments documents) =
      some documents := by
  induction documents with
  | nil => rfl
  | cons document documents inductionHypothesis =>
      simp [encodeSourceDocuments, decodeSourceDocumentsShape?, a,
        inductionHypothesis]

@[simp] theorem decodeIncludeBindingShape_encodeIncludeBinding
    (binding : IncludeBinding) :
    decodeIncludeBindingShape? (encodeIncludeBinding binding) =
      some binding := by
  cases binding
  rfl

@[simp] theorem decodeIncludeBindingsShape_encodeIncludeBindings
    (bindings : List IncludeBinding) :
    decodeIncludeBindingsShape? (encodeIncludeBindings bindings) =
      some bindings := by
  induction bindings with
  | nil => rfl
  | cons binding bindings inductionHypothesis =>
      simp [encodeIncludeBindings, decodeIncludeBindingsShape?, a,
        inductionHypothesis]

@[simp] theorem decodeSourceEnvironmentShape_encodeSourceEnvironment
    (environment : SourceEnvironment) :
    decodeSourceEnvironmentShape? (encodeSourceEnvironment environment) =
      some environment := by
  cases environment
  simp [encodeSourceEnvironment, decodeSourceEnvironmentShape?, a]

theorem encodeSourceEnvironment_injective :
    Function.Injective encodeSourceEnvironment := by
  intro first second equalEncoding
  have decoded := congrArg decodeSourceEnvironmentShape? equalEncoding
  simpa only [decodeSourceEnvironmentShape_encodeSourceEnvironment,
    Option.some.injEq] using decoded

/-! ## Typed admission -/

def sourceDocumentWellSorted (document : SourceDocument) : Bool :=
  CarrierWellSorted.checkHasType TptpOfficialAbstractSyntax.language
    WellSorted.FreeTypeContext.empty [] document.officialFile
    (.base "Tptp92Ast:tptp-file")

def sourceEnvironmentWellSorted (environment : SourceEnvironment) : Bool :=
  environment.documents.all sourceDocumentWellSorted

/-- Decode the carrier shape and reject any embedded file outside the official
TPTP abstract-syntax root sort.  Uniqueness and include-graph conditions are
deliberately left to `resolve?`. -/
def decodeSourceEnvironment? (pattern : Pattern) : Option SourceEnvironment := do
  let environment <- decodeSourceEnvironmentShape? pattern
  if sourceEnvironmentWellSorted environment then
    some environment
  else
    none

theorem decodeSourceEnvironment_encodeSourceEnvironment
    (environment : SourceEnvironment)
    (wellSorted : sourceEnvironmentWellSorted environment = true) :
    decodeSourceEnvironment? (encodeSourceEnvironment environment) =
      some environment := by
  simp [decodeSourceEnvironment?, wellSorted]

/-! ## Positive and adversarial controls -/

namespace Canary

theorem nested_environment_shape_round_trip :
    decodeSourceEnvironmentShape?
        (encodeSourceEnvironment
          TptpOfficialIncludeResolution.Canary.nestedEnvironment) =
      some TptpOfficialIncludeResolution.Canary.nestedEnvironment := by
  exact decodeSourceEnvironmentShape_encodeSourceEnvironment _

def admittedDocument : SourceDocument := {
  canonicalId := "admitted-root"
  digest := "admitted-root-digest"
  officialFile := TptpOfficialAbstractSyntax.emptyFile
}

def admittedEnvironment : SourceEnvironment := {
  documents := [admittedDocument]
  bindings := []
}

theorem admitted_document_well_sorted :
    sourceDocumentWellSorted admittedDocument = true := by
  change CarrierWellSorted.checkHasType TptpOfficialAbstractSyntax.language
    WellSorted.FreeTypeContext.empty [] TptpOfficialAbstractSyntax.emptyFile
      (.base "Tptp92Ast:tptp-file") = true
  exact TptpOfficialAbstractSyntax.empty_file_inhabits_root

theorem admitted_environment_well_sorted :
    sourceEnvironmentWellSorted admittedEnvironment = true := by
  simp only [sourceEnvironmentWellSorted, admittedEnvironment,
    List.all_cons, List.all_nil, Bool.and_true]
  exact admitted_document_well_sorted

theorem admitted_environment_decodes_exactly :
    decodeSourceEnvironment?
        (encodeSourceEnvironment admittedEnvironment) =
      some admittedEnvironment := by
  exact decodeSourceEnvironment_encodeSourceEnvironment _
    admitted_environment_well_sorted

theorem admitted_environment_inhabits_carrier :
    CarrierWellSorted.checkHasType language WellSorted.FreeTypeContext.empty []
        (encodeSourceEnvironment admittedEnvironment)
        (.base "TptpIncludeResolution:SourceEnvironment") = true := by
  decide +kernel

theorem malformed_outer_constructor_is_rejected :
    decodeSourceEnvironment? (a "not-a-source-environment") = none := by
  rfl

theorem malformed_official_file_is_not_well_sorted :
    sourceEnvironmentWellSorted
      TptpOfficialIncludeResolution.Canary.malformedDocumentEnvironment =
        false := by
  decide +kernel

theorem malformed_official_file_is_rejected :
    decodeSourceEnvironment?
        (encodeSourceEnvironment
          TptpOfficialIncludeResolution.Canary.malformedDocumentEnvironment) =
      none := by
  decide +kernel

theorem malformed_official_file_does_not_inhabit_carrier :
    CarrierWellSorted.checkHasType language WellSorted.FreeTypeContext.empty []
        (encodeSourceEnvironment
          TptpOfficialIncludeResolution.Canary.malformedDocumentEnvironment)
        (.base "TptpIncludeResolution:SourceEnvironment") = false := by
  decide +kernel

def otherAdmittedDocument : SourceDocument := {
  canonicalId := "admitted-root"
  digest := "other-admitted-root-digest"
  officialFile := TptpOfficialAbstractSyntax.emptyFile
}

theorem other_admitted_document_well_sorted :
    sourceDocumentWellSorted otherAdmittedDocument = true := by
  change CarrierWellSorted.checkHasType TptpOfficialAbstractSyntax.language
    WellSorted.FreeTypeContext.empty [] TptpOfficialAbstractSyntax.emptyFile
      (.base "Tptp92Ast:tptp-file") = true
  exact TptpOfficialAbstractSyntax.empty_file_inhabits_root

def ambiguousAdmittedEnvironment : SourceEnvironment := {
  documents := [admittedDocument, otherAdmittedDocument]
  bindings := []
}

theorem ambiguous_documents_remain_typed_data :
    sourceEnvironmentWellSorted
      ambiguousAdmittedEnvironment = true := by
  simp only [sourceEnvironmentWellSorted, ambiguousAdmittedEnvironment,
    List.all_cons, List.all_nil, admitted_document_well_sorted,
    other_admitted_document_well_sorted, Bool.and_self]

theorem ambiguous_documents_decode_before_semantic_rejection :
    decodeSourceEnvironment?
        (encodeSourceEnvironment ambiguousAdmittedEnvironment) =
      some ambiguousAdmittedEnvironment := by
  exact decodeSourceEnvironment_encodeSourceEnvironment _
    ambiguous_documents_remain_typed_data

theorem ambiguous_documents_fail_in_resolver :
    resolve? ambiguousAdmittedEnvironment "admitted-root" =
      .error (.ambiguousDocument "admitted-root") := by
  rfl

end Canary

#print axioms language_validate
#print axioms language_supported
#print axioms decodeSourceEnvironmentShape_encodeSourceEnvironment
#print axioms encodeSourceEnvironment_injective
#print axioms decodeSourceEnvironment_encodeSourceEnvironment
#print axioms Canary.nested_environment_shape_round_trip
#print axioms Canary.admitted_environment_decodes_exactly
#print axioms Canary.admitted_environment_inhabits_carrier
#print axioms Canary.malformed_official_file_is_rejected
#print axioms Canary.malformed_official_file_does_not_inhabit_carrier
#print axioms Canary.ambiguous_documents_decode_before_semantic_rejection
#print axioms Canary.ambiguous_documents_fail_in_resolver

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionCarrier
