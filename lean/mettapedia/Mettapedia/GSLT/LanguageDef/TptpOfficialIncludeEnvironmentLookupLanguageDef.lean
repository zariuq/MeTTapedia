import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolutionResultCarrier
import Mettapedia.GSLT.LanguageDef.PatternEqualityDecision
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
import Mettapedia.GSLT.LanguageDef.RewriteValidationCertificateExtension
import Mettapedia.GSLT.LanguageDef.ConstructorSignatureExtension
import Mettapedia.GSLT.LanguageDef.CanonicalWire
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Declared lookup for TPTP include environments

The include resolver consults two finite tables at the root and at every
include edge: canonical source documents and parent-relative include bindings.
This `LanguageDef` declares those lookups without calling the host resolver.
It distinguishes zero, one, and multiple matches so missing and ambiguous
entries remain different failures.

String equality is supplied by the generic `PatternEqualityDecision` relation.
The rules preserve source-list order and return the unique original document or
binding occurrence rather than reconstructing an equivalent record.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupLanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution

namespace Carrier

abbrev language :=
  TptpOfficialIncludeResolutionResultCarrier.language
abbrev encodeString :=
  TptpOfficialIncludeResolutionResultCarrier.encodeString
abbrev encodeSourceDocument :=
  TptpOfficialIncludeResolutionCarrier.encodeSourceDocument
abbrev encodeIncludeBinding :=
  TptpOfficialIncludeResolutionCarrier.encodeIncludeBinding
abbrev encodeSourceEnvironment :=
  TptpOfficialIncludeResolutionCarrier.encodeSourceEnvironment
abbrev encodeResolutionError :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolutionError

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

def sourceEnvironment (documents bindings : Pattern) : Pattern :=
  a "tptp-include-resolution:source-environment" [documents, bindings]

def sourceDocumentsNil : Pattern :=
  a "tptp-include-resolution:source-documents-nil"

def sourceDocumentsCons (head tail : Pattern) : Pattern :=
  a "tptp-include-resolution:source-documents-cons" [head, tail]

def sourceDocument (canonicalId digest officialFile : Pattern) : Pattern :=
  a "tptp-include-resolution:source-document"
    [canonicalId, digest, officialFile]

def includeBindingsNil : Pattern :=
  a "tptp-include-resolution:include-bindings-nil"

def includeBindingsCons (head tail : Pattern) : Pattern :=
  a "tptp-include-resolution:include-bindings-cons" [head, tail]

def includeBinding (fromSource requestedFile targetSource : Pattern) : Pattern :=
  a "tptp-include-resolution:include-binding"
    [fromSource, requestedFile, targetSource]

def errorMissingDocument (canonicalId : Pattern) : Pattern :=
  a "tptp-include-result:error-missing-document" [canonicalId]

def errorAmbiguousDocument (canonicalId : Pattern) : Pattern :=
  a "tptp-include-result:error-ambiguous-document" [canonicalId]

def errorMissingBinding (fromSource requestedFile : Pattern) : Pattern :=
  a "tptp-include-result:error-missing-binding"
    [fromSource, requestedFile]

def errorAmbiguousBinding (fromSource requestedFile : Pattern) : Pattern :=
  a "tptp-include-result:error-ambiguous-binding"
    [fromSource, requestedFile]

def documentNone : Pattern := a "tptp-include-lookup:document-none"
def documentOne (document : Pattern) : Pattern :=
  a "tptp-include-lookup:document-one" [document]
def documentMany : Pattern := a "tptp-include-lookup:document-many"

def bindingNone : Pattern := a "tptp-include-lookup:binding-none"
def bindingOne (binding : Pattern) : Pattern :=
  a "tptp-include-lookup:binding-one" [binding]
def bindingMany : Pattern := a "tptp-include-lookup:binding-many"

def documentOk (document : Pattern) : Pattern :=
  a "tptp-include-lookup:document-ok" [document]
def documentError (failure : Pattern) : Pattern :=
  a "tptp-include-lookup:document-error" [failure]
def bindingOk (binding : Pattern) : Pattern :=
  a "tptp-include-lookup:binding-ok" [binding]
def bindingError (failure : Pattern) : Pattern :=
  a "tptp-include-lookup:binding-error" [failure]

def lookupDocument (canonicalId environment : Pattern) : Pattern :=
  a "tptp-include-lookup:lookup-document" [canonicalId, environment]
def scanDocuments (canonicalId documents : Pattern) : Pattern :=
  a "tptp-include-lookup:scan-documents" [canonicalId, documents]
def documentDecision (decision document tail : Pattern) : Pattern :=
  a "tptp-include-lookup:document-decision" [decision, document, tail]
def finishDocument (canonicalId count : Pattern) : Pattern :=
  a "tptp-include-lookup:finish-document" [canonicalId, count]

def lookupBinding (fromSource requestedFile environment : Pattern) : Pattern :=
  a "tptp-include-lookup:lookup-binding"
    [fromSource, requestedFile, environment]
def scanBindings (fromSource requestedFile bindings : Pattern) : Pattern :=
  a "tptp-include-lookup:scan-bindings"
    [fromSource, requestedFile, bindings]
def bindingFromDecision (decision requestedFile binding tail : Pattern) : Pattern :=
  a "tptp-include-lookup:binding-from-decision"
    [decision, requestedFile, binding, tail]
def bindingRequestDecision (decision binding tail : Pattern) : Pattern :=
  a "tptp-include-lookup:binding-request-decision" [decision, binding, tail]
def finishBinding (fromSource requestedFile count : Pattern) : Pattern :=
  a "tptp-include-lookup:finish-binding" [fromSource, requestedFile, count]

def supportTypes : List TypeDecl := [
  TypeDecl.plain "TptpIncludeLookup:DocumentCount",
  TypeDecl.plain "TptpIncludeLookup:BindingCount",
  TypeDecl.plain "TptpIncludeLookup:DocumentOutcome",
  TypeDecl.plain "TptpIncludeLookup:BindingOutcome"]

def supportTerms : List GrammarRule := [
  ctor "tptp-include-lookup:document-none"
    "TptpIncludeLookup:DocumentCount" [],
  ctor "tptp-include-lookup:document-one"
    "TptpIncludeLookup:DocumentCount"
    [("document", "TptpIncludeResolution:SourceDocument")],
  ctor "tptp-include-lookup:document-many"
    "TptpIncludeLookup:DocumentCount" [],
  ctor "tptp-include-lookup:binding-none"
    "TptpIncludeLookup:BindingCount" [],
  ctor "tptp-include-lookup:binding-one"
    "TptpIncludeLookup:BindingCount"
    [("binding", "TptpIncludeResolution:IncludeBinding")],
  ctor "tptp-include-lookup:binding-many"
    "TptpIncludeLookup:BindingCount" [],
  ctor "tptp-include-lookup:document-ok"
    "TptpIncludeLookup:DocumentOutcome"
    [("document", "TptpIncludeResolution:SourceDocument")],
  ctor "tptp-include-lookup:document-error"
    "TptpIncludeLookup:DocumentOutcome"
    [("failure", "TptpIncludeResult:ResolutionError")],
  ctor "tptp-include-lookup:binding-ok"
    "TptpIncludeLookup:BindingOutcome"
    [("binding", "TptpIncludeResolution:IncludeBinding")],
  ctor "tptp-include-lookup:binding-error"
    "TptpIncludeLookup:BindingOutcome"
    [("failure", "TptpIncludeResult:ResolutionError")],
  ctor "tptp-include-lookup:lookup-document"
    "TptpIncludeLookup:DocumentOutcome"
    [("canonical-id", "String"),
      ("environment", "TptpIncludeResolution:SourceEnvironment")]
    (some .rewrite),
  ctor "tptp-include-lookup:scan-documents"
    "TptpIncludeLookup:DocumentCount"
    [("canonical-id", "String"),
      ("documents", "TptpIncludeResolution:SourceDocuments")]
    (some .rewrite),
  ctor "tptp-include-lookup:document-decision"
    "TptpIncludeLookup:DocumentCount"
    [("decision", "PatternEqualityDecision:Result"),
      ("document", "TptpIncludeResolution:SourceDocument"),
      ("tail", "TptpIncludeLookup:DocumentCount")]
    (some .rewrite),
  ctor "tptp-include-lookup:finish-document"
    "TptpIncludeLookup:DocumentOutcome"
    [("canonical-id", "String"),
      ("count", "TptpIncludeLookup:DocumentCount")]
    (some .rewrite),
  ctor "tptp-include-lookup:lookup-binding"
    "TptpIncludeLookup:BindingOutcome"
    [("from-source", "String"), ("requested-file", "String"),
      ("environment", "TptpIncludeResolution:SourceEnvironment")]
    (some .rewrite),
  ctor "tptp-include-lookup:scan-bindings"
    "TptpIncludeLookup:BindingCount"
    [("from-source", "String"), ("requested-file", "String"),
      ("bindings", "TptpIncludeResolution:IncludeBindings")]
    (some .rewrite),
  ctor "tptp-include-lookup:binding-from-decision"
    "TptpIncludeLookup:BindingCount"
    [("decision", "PatternEqualityDecision:Result"),
      ("requested-file", "String"),
      ("binding", "TptpIncludeResolution:IncludeBinding"),
      ("tail", "TptpIncludeLookup:BindingCount")]
    (some .rewrite),
  ctor "tptp-include-lookup:binding-request-decision"
    "TptpIncludeLookup:BindingCount"
    [("decision", "PatternEqualityDecision:Result"),
      ("binding", "TptpIncludeResolution:IncludeBinding"),
      ("tail", "TptpIncludeLookup:BindingCount")]
    (some .rewrite),
  ctor "tptp-include-lookup:finish-binding"
    "TptpIncludeLookup:BindingOutcome"
    [("from-source", "String"), ("requested-file", "String"),
      ("count", "TptpIncludeLookup:BindingCount")]
    (some .rewrite)]

def documentRules : List RewriteRule := [
  mkRule "tptp-include-lookup:lookup-document"
    [("canonicalId", "String"),
      ("documents", "TptpIncludeResolution:SourceDocuments"),
      ("bindings", "TptpIncludeResolution:IncludeBindings"),
      ("count", "TptpIncludeLookup:DocumentCount"),
      ("result", "TptpIncludeLookup:DocumentOutcome")]
    [congruence (scanDocuments (v "canonicalId") (v "documents"))
        (v "count"),
      congruence (finishDocument (v "canonicalId") (v "count"))
        (v "result")]
    (lookupDocument (v "canonicalId")
      (sourceEnvironment (v "documents") (v "bindings")))
    (v "result"),
  mkRule "tptp-include-lookup:scan-documents-nil"
    [("canonicalId", "String")] []
    (scanDocuments (v "canonicalId") sourceDocumentsNil) documentNone,
  mkRule "tptp-include-lookup:scan-documents-cons"
    [("canonicalId", "String"), ("documentId", "String"),
      ("digest", "String"), ("officialFile", "Tptp92Ast:tptp-file"),
      ("documents", "TptpIncludeResolution:SourceDocuments"),
      ("decision", "PatternEqualityDecision:Result"),
      ("tail", "TptpIncludeLookup:DocumentCount"),
      ("result", "TptpIncludeLookup:DocumentCount")]
    [.relationQuery PatternEqualityDecision.relationName
        [v "canonicalId", v "documentId", v "decision"],
      congruence (scanDocuments (v "canonicalId") (v "documents"))
        (v "tail"),
      congruence
        (documentDecision (v "decision")
          (sourceDocument (v "documentId") (v "digest") (v "officialFile"))
          (v "tail")) (v "result")]
    (scanDocuments (v "canonicalId")
      (sourceDocumentsCons
        (sourceDocument (v "documentId") (v "digest") (v "officialFile"))
        (v "documents")))
    (v "result"),
  mkRule "tptp-include-lookup:document-different"
    [("document", "TptpIncludeResolution:SourceDocument"),
      ("tail", "TptpIncludeLookup:DocumentCount")] []
    (documentDecision PatternEqualityDecision.different
      (v "document") (v "tail")) (v "tail"),
  mkRule "tptp-include-lookup:document-first"
    [("document", "TptpIncludeResolution:SourceDocument")] []
    (documentDecision PatternEqualityDecision.equal
      (v "document") documentNone) (documentOne (v "document")),
  mkRule "tptp-include-lookup:document-second"
    [("document", "TptpIncludeResolution:SourceDocument"),
      ("existing", "TptpIncludeResolution:SourceDocument")] []
    (documentDecision PatternEqualityDecision.equal
      (v "document") (documentOne (v "existing"))) documentMany,
  mkRule "tptp-include-lookup:document-already-many"
    [("document", "TptpIncludeResolution:SourceDocument")] []
    (documentDecision PatternEqualityDecision.equal
      (v "document") documentMany) documentMany,
  mkRule "tptp-include-lookup:finish-document-missing"
    [("canonicalId", "String")] []
    (finishDocument (v "canonicalId") documentNone)
    (documentError (errorMissingDocument (v "canonicalId"))),
  mkRule "tptp-include-lookup:finish-document-one"
    [("canonicalId", "String"),
      ("document", "TptpIncludeResolution:SourceDocument")] []
    (finishDocument (v "canonicalId") (documentOne (v "document")))
    (documentOk (v "document")),
  mkRule "tptp-include-lookup:finish-document-ambiguous"
    [("canonicalId", "String")] []
    (finishDocument (v "canonicalId") documentMany)
    (documentError (errorAmbiguousDocument (v "canonicalId")))]

def bindingRules : List RewriteRule := [
  mkRule "tptp-include-lookup:lookup-binding"
    [("fromSource", "String"), ("requestedFile", "String"),
      ("documents", "TptpIncludeResolution:SourceDocuments"),
      ("bindings", "TptpIncludeResolution:IncludeBindings"),
      ("count", "TptpIncludeLookup:BindingCount"),
      ("result", "TptpIncludeLookup:BindingOutcome")]
    [congruence
        (scanBindings (v "fromSource") (v "requestedFile") (v "bindings"))
        (v "count"),
      congruence
        (finishBinding (v "fromSource") (v "requestedFile") (v "count"))
        (v "result")]
    (lookupBinding (v "fromSource") (v "requestedFile")
      (sourceEnvironment (v "documents") (v "bindings")))
    (v "result"),
  mkRule "tptp-include-lookup:scan-bindings-nil"
    [("fromSource", "String"), ("requestedFile", "String")] []
    (scanBindings (v "fromSource") (v "requestedFile") includeBindingsNil)
    bindingNone,
  mkRule "tptp-include-lookup:scan-bindings-cons"
    [("fromSource", "String"), ("requestedFile", "String"),
      ("bindingFrom", "String"), ("bindingRequested", "String"),
      ("targetSource", "String"),
      ("bindings", "TptpIncludeResolution:IncludeBindings"),
      ("decision", "PatternEqualityDecision:Result"),
      ("tail", "TptpIncludeLookup:BindingCount"),
      ("result", "TptpIncludeLookup:BindingCount")]
    [.relationQuery PatternEqualityDecision.relationName
        [v "fromSource", v "bindingFrom", v "decision"],
      congruence
        (scanBindings (v "fromSource") (v "requestedFile") (v "bindings"))
        (v "tail"),
      congruence
        (bindingFromDecision (v "decision") (v "requestedFile")
          (includeBinding (v "bindingFrom") (v "bindingRequested")
            (v "targetSource")) (v "tail"))
        (v "result")]
    (scanBindings (v "fromSource") (v "requestedFile")
      (includeBindingsCons
        (includeBinding (v "bindingFrom") (v "bindingRequested")
          (v "targetSource")) (v "bindings")))
    (v "result"),
  mkRule "tptp-include-lookup:binding-from-different"
    [("requestedFile", "String"),
      ("binding", "TptpIncludeResolution:IncludeBinding"),
      ("tail", "TptpIncludeLookup:BindingCount")] []
    (bindingFromDecision PatternEqualityDecision.different
      (v "requestedFile") (v "binding") (v "tail")) (v "tail"),
  mkRule "tptp-include-lookup:binding-from-equal"
    [("requestedFile", "String"), ("bindingFrom", "String"),
      ("bindingRequested", "String"), ("targetSource", "String"),
      ("tail", "TptpIncludeLookup:BindingCount"),
      ("decision", "PatternEqualityDecision:Result"),
      ("result", "TptpIncludeLookup:BindingCount")]
    [.relationQuery PatternEqualityDecision.relationName
        [v "requestedFile", v "bindingRequested", v "decision"],
      congruence
        (bindingRequestDecision (v "decision")
          (includeBinding (v "bindingFrom") (v "bindingRequested")
            (v "targetSource")) (v "tail"))
        (v "result")]
    (bindingFromDecision PatternEqualityDecision.equal (v "requestedFile")
      (includeBinding (v "bindingFrom") (v "bindingRequested")
        (v "targetSource")) (v "tail"))
    (v "result"),
  mkRule "tptp-include-lookup:binding-request-different"
    [("binding", "TptpIncludeResolution:IncludeBinding"),
      ("tail", "TptpIncludeLookup:BindingCount")] []
    (bindingRequestDecision PatternEqualityDecision.different
      (v "binding") (v "tail")) (v "tail"),
  mkRule "tptp-include-lookup:binding-first"
    [("binding", "TptpIncludeResolution:IncludeBinding")] []
    (bindingRequestDecision PatternEqualityDecision.equal
      (v "binding") bindingNone) (bindingOne (v "binding")),
  mkRule "tptp-include-lookup:binding-second"
    [("binding", "TptpIncludeResolution:IncludeBinding"),
      ("existing", "TptpIncludeResolution:IncludeBinding")] []
    (bindingRequestDecision PatternEqualityDecision.equal
      (v "binding") (bindingOne (v "existing"))) bindingMany,
  mkRule "tptp-include-lookup:binding-already-many"
    [("binding", "TptpIncludeResolution:IncludeBinding")] []
    (bindingRequestDecision PatternEqualityDecision.equal
      (v "binding") bindingMany) bindingMany,
  mkRule "tptp-include-lookup:finish-binding-missing"
    [("fromSource", "String"), ("requestedFile", "String")] []
    (finishBinding (v "fromSource") (v "requestedFile") bindingNone)
    (bindingError (errorMissingBinding
      (v "fromSource") (v "requestedFile"))),
  mkRule "tptp-include-lookup:finish-binding-one"
    [("fromSource", "String"), ("requestedFile", "String"),
      ("binding", "TptpIncludeResolution:IncludeBinding")] []
    (finishBinding (v "fromSource") (v "requestedFile")
      (bindingOne (v "binding"))) (bindingOk (v "binding")),
  mkRule "tptp-include-lookup:finish-binding-ambiguous"
    [("fromSource", "String"), ("requestedFile", "String")] []
    (finishBinding (v "fromSource") (v "requestedFile") bindingMany)
    (bindingError (errorAmbiguousBinding
      (v "fromSource") (v "requestedFile")))]

def rewrites : List RewriteRule := documentRules ++ bindingRules

private def addedTypes : List TypeDecl :=
  PatternEqualityDecision.language.types ++ supportTypes

private def addedTerms : List GrammarRule :=
  PatternEqualityDecision.language.terms ++ supportTerms

private def signatureBase : CalculusLanguageDef :=
  CalculusLanguageDef.extend Carrier.language {}

private def signatureExtension : CalculusLanguageExtension :=
  ConstructorSignatureExtension.ofLists addedTypes addedTerms
    (some "TptpOfficialIncludeEnvironmentLookupV1")

private def signatureCalculusLanguage : CalculusLanguageDef :=
  signatureExtension.apply signatureBase

def signatureLanguage : LanguageDef :=
  signatureCalculusLanguage.toLanguageDef

def language : LanguageDef := {
  name := "TptpOfficialIncludeEnvironmentLookupV1"
  types := signatureLanguage.types
  terms := signatureLanguage.terms
  equations := []
  rewrites
}

@[simp] theorem typeNames_exact :
    language.typeNames = Carrier.language.typeNames ++
      (PatternEqualityDecision.language.types ++ supportTypes).map
        (·.name) := by
  simp [language, signatureLanguage, signatureCalculusLanguage,
    signatureExtension, signatureBase, ConstructorSignatureExtension.ofLists,
    addedTypes, LanguageDef.typeNames]

@[simp] theorem constructorSignatures_exact :
    RewriteValidationCertificate.constructorSignatures language =
      RewriteValidationCertificate.constructorSignatures Carrier.language ++
      (PatternEqualityDecision.language.terms ++ supportTerms).map fun declaration =>
        (declaration.label, declaration.params.length) := by
  simp [RewriteValidationCertificate.constructorSignatures, language,
    signatureLanguage, signatureCalculusLanguage, signatureExtension,
    signatureBase, ConstructorSignatureExtension.ofLists, addedTerms]

@[simp] theorem language_rewrites : language.rewrites = rewrites := rfl

theorem rewrite_count : rewrites.length = 22 := by
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
            !(name.startsWith "TptpIncludeLookup:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTypes.map (·.name)).all
        (fun name =>
          name.startsWith "PatternEqualityDecision:" ||
            name.startsWith "TptpIncludeLookup:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro name sourceMembership addedMembership
  have base := (List.all_eq_true.mp baseSeparate) name sourceMembership
  have added := (List.all_eq_true.mp addedNamespaced) name addedMembership
  simp only [Bool.and_eq_true, Bool.or_eq_true] at base added
  rcases base with ⟨notEquality, notLookup⟩
  rcases added with equality | lookup
  · simp [equality] at notEquality
  · simp [lookup] at notLookup

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
            !(label.startsWith "tptp-include-lookup:")) = true := by
    decide +kernel
  have addedNamespaced :
      (addedTerms.map (·.label)).all
        (fun label =>
          label.startsWith "pattern-equality-decision:" ||
            label.startsWith "tptp-include-lookup:") = true := by
    decide +kernel
  rw [List.disjoint_left]
  intro label sourceMembership addedMembership
  have base := (List.all_eq_true.mp baseSeparate) label sourceMembership
  have added := (List.all_eq_true.mp addedNamespaced) label addedMembership
  simp only [Bool.and_eq_true, Bool.or_eq_true] at base added
  rcases base with ⟨notEquality, notLookup⟩
  rcases added with equality | lookup
  · simp [equality] at notEquality
  · simp [lookup] at notLookup

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
      (some "TptpOfficialIncludeEnvironmentLookupV1")
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
  "String", "Tptp92Ast:tptp-file",
  "TptpIncludeResolution:SourceDocument",
  "TptpIncludeResolution:SourceDocuments",
  "TptpIncludeResolution:IncludeBinding",
  "TptpIncludeResolution:IncludeBindings",
  "TptpIncludeResolution:SourceEnvironment",
  "TptpIncludeResult:ResolutionError",
  "PatternEqualityDecision:Result",
  "TptpIncludeLookup:DocumentCount",
  "TptpIncludeLookup:BindingCount",
  "TptpIncludeLookup:DocumentOutcome",
  "TptpIncludeLookup:BindingOutcome"]

private theorem requiredTypes_declared :
    requiredTypes.all (fun name => decide (name ∈ language.typeNames)) =
      true := by
  decide +kernel

private theorem requiredType_declared (name : String)
    (membership : name ∈ requiredTypes) : name ∈ language.typeNames :=
  decide_eq_true_eq.mp
    (List.all_eq_true.mp requiredTypes_declared name membership)

private def requiredSignatures : List (String × Nat) := [
  ("tptp-include-resolution:source-environment", 2),
  ("tptp-include-resolution:source-documents-nil", 0),
  ("tptp-include-resolution:source-documents-cons", 2),
  ("tptp-include-resolution:source-document", 3),
  ("tptp-include-resolution:include-bindings-nil", 0),
  ("tptp-include-resolution:include-bindings-cons", 2),
  ("tptp-include-resolution:include-binding", 3),
  ("tptp-include-result:error-missing-document", 1),
  ("tptp-include-result:error-ambiguous-document", 1),
  ("tptp-include-result:error-missing-binding", 2),
  ("tptp-include-result:error-ambiguous-binding", 2),
  ("pattern-equality-decision:equal", 0),
  ("pattern-equality-decision:different", 0),
  ("tptp-include-lookup:document-none", 0),
  ("tptp-include-lookup:document-one", 1),
  ("tptp-include-lookup:document-many", 0),
  ("tptp-include-lookup:binding-none", 0),
  ("tptp-include-lookup:binding-one", 1),
  ("tptp-include-lookup:binding-many", 0),
  ("tptp-include-lookup:document-ok", 1),
  ("tptp-include-lookup:document-error", 1),
  ("tptp-include-lookup:binding-ok", 1),
  ("tptp-include-lookup:binding-error", 1),
  ("tptp-include-lookup:lookup-document", 2),
  ("tptp-include-lookup:scan-documents", 2),
  ("tptp-include-lookup:document-decision", 3),
  ("tptp-include-lookup:finish-document", 2),
  ("tptp-include-lookup:lookup-binding", 3),
  ("tptp-include-lookup:scan-bindings", 3),
  ("tptp-include-lookup:binding-from-decision", 4),
  ("tptp-include-lookup:binding-request-decision", 3),
  ("tptp-include-lookup:finish-binding", 3)]

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

local macro "certify_lookup_rows" : tactic =>
  `(tactic|
    simp [subsetCheck, contextSubsetCheck, patternSubsetCheck,
      premisesSubsetCheck, fvarsPlainCheck, bindersPlainCheck,
      contextNamesPlainCheck, documentRules, bindingRules,
      sourceEnvironment, sourceDocumentsNil, sourceDocumentsCons,
      sourceDocument, includeBindingsNil, includeBindingsCons, includeBinding,
      errorMissingDocument, errorAmbiguousDocument,
      errorMissingBinding, errorAmbiguousBinding,
      documentNone, documentOne, documentMany,
      bindingNone, bindingOne, bindingMany,
      documentOk, documentError, bindingOk, bindingError,
      lookupDocument, scanDocuments, documentDecision, finishDocument,
      lookupBinding, scanBindings, bindingFromDecision,
      bindingRequestDecision, finishBinding,
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
      PatternEqualityDecision.equal, PatternEqualityDecision.different,
      RewriteValidationCertificate.allPatternsScopedCheck,
      RewriteValidationCertificate.rightBoundCheck])

private theorem document_subset_checked :
    documentRules.all subsetCheck = true := by
  certify_lookup_rows

private theorem binding_subset_checked :
    bindingRules.all subsetCheck = true := by
  certify_lookup_rows

private theorem every_rewrite_subset_checked :
    rewrites.all subsetCheck = true := by
  simp only [rewrites, List.all_append, document_subset_checked,
    binding_subset_checked, Bool.and_self]

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
    language.terms = Carrier.language.terms ++ addedTerms := by
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

def relations : RelationEnv := PatternEqualityDecision.relationEnv

def encodeDocumentOutcome :
    Except ResolutionError SourceDocument -> Pattern
  | .error failure =>
      documentError (Carrier.encodeResolutionError failure)
  | .ok document => documentOk (Carrier.encodeSourceDocument document)

def encodeBindingOutcome :
    Except ResolutionError IncludeBinding -> Pattern
  | .error failure =>
      bindingError (Carrier.encodeResolutionError failure)
  | .ok binding => bindingOk (Carrier.encodeIncludeBinding binding)

def encodeDocumentRequest (environment : SourceEnvironment)
    (canonicalId : String) : Pattern :=
  lookupDocument (Carrier.encodeString canonicalId)
    (Carrier.encodeSourceEnvironment environment)

def encodeBindingRequest (environment : SourceEnvironment)
    (fromSource requestedFile : String) : Pattern :=
  lookupBinding (Carrier.encodeString fromSource)
    (Carrier.encodeString requestedFile)
    (Carrier.encodeSourceEnvironment environment)

#print axioms rewrite_count
#print axioms language_validate
#print axioms language_supported

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupLanguageDef
