import Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupLanguageDef
import Mettapedia.OSLF.MeTTaIL.ContextualRootDispatch

/-!
# Exact agreement for TPTP include-environment lookup

This module proves that the declared environment-lookup language implements
the independent finite-list lookup used by the include resolver.  The proof is
for arbitrary admitted environments.  It preserves the unique source record
and distinguishes missing from ambiguous documents and parent-relative
bindings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeResolution
open Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupLanguageDef

namespace Carrier

abbrev encodeString :=
  TptpOfficialIncludeResolutionResultCarrier.encodeString
abbrev encodeSourceDocument :=
  TptpOfficialIncludeResolutionCarrier.encodeSourceDocument
abbrev encodeSourceDocuments :=
  TptpOfficialIncludeResolutionCarrier.encodeSourceDocuments
abbrev encodeIncludeBinding :=
  TptpOfficialIncludeResolutionCarrier.encodeIncludeBinding
abbrev encodeIncludeBindings :=
  TptpOfficialIncludeResolutionCarrier.encodeIncludeBindings
abbrev encodeSourceEnvironment :=
  TptpOfficialIncludeResolutionCarrier.encodeSourceEnvironment
abbrev encodeResolutionError :=
  TptpOfficialIncludeResolutionResultCarrier.encodeResolutionError

end Carrier

@[simp] private theorem encodeResolutionError_missingDocument
    (canonicalId : String) :
    Carrier.encodeResolutionError (.missingDocument canonicalId) =
      errorMissingDocument (Carrier.encodeString canonicalId) := by
  rfl

@[simp] private theorem encodeResolutionError_ambiguousDocument
    (canonicalId : String) :
    Carrier.encodeResolutionError (.ambiguousDocument canonicalId) =
      errorAmbiguousDocument (Carrier.encodeString canonicalId) := by
  rfl

@[simp] private theorem encodeResolutionError_missingBinding
    (fromSource requestedFile : String) :
    Carrier.encodeResolutionError (.missingBinding fromSource requestedFile) =
      errorMissingBinding (Carrier.encodeString fromSource)
        (Carrier.encodeString requestedFile) := by
  rfl

@[simp] private theorem encodeResolutionError_ambiguousBinding
    (fromSource requestedFile : String) :
    Carrier.encodeResolutionError (.ambiguousBinding fromSource requestedFile) =
      errorAmbiguousBinding (Carrier.encodeString fromSource)
        (Carrier.encodeString requestedFile) := by
  rfl

@[simp] private theorem encodeSourceDocument_eq
    (canonicalId digest : String) (officialFile : Pattern) :
    Carrier.encodeSourceDocument
        { canonicalId := canonicalId, digest, officialFile } =
      sourceDocument (Carrier.encodeString canonicalId)
        (Carrier.encodeString digest) officialFile := by
  rfl

@[simp] private theorem encodeSourceDocuments_cons
    (document : SourceDocument) (documents : List SourceDocument) :
    Carrier.encodeSourceDocuments (document :: documents) =
      sourceDocumentsCons (Carrier.encodeSourceDocument document)
        (Carrier.encodeSourceDocuments documents) := by
  rfl

@[simp] private theorem encodeIncludeBinding_eq
    (fromSource requestedFile targetSource : String) :
    Carrier.encodeIncludeBinding
        { fromSource, requestedFile, targetSource } =
      includeBinding (Carrier.encodeString fromSource)
        (Carrier.encodeString requestedFile)
        (Carrier.encodeString targetSource) := by
  rfl

@[simp] private theorem encodeIncludeBindings_cons
    (binding : IncludeBinding) (bindings : List IncludeBinding) :
    Carrier.encodeIncludeBindings (binding :: bindings) =
      includeBindingsCons (Carrier.encodeIncludeBinding binding)
        (Carrier.encodeIncludeBindings bindings) := by
  rfl

/-! ## Independent finite-match classification -/

inductive FiniteMatch (α : Type) where
  | none
  | one (value : α)
  | many
  deriving DecidableEq, Repr

def FiniteMatch.ofList {α : Type} : List α → FiniteMatch α
  | [] => .none
  | [value] => .one value
  | _ :: _ :: _ => .many

def FiniteMatch.add {α : Type} (value : α) : FiniteMatch α → FiniteMatch α
  | .none => .one value
  | .one _ => .many
  | .many => .many

@[simp] theorem FiniteMatch.ofList_cons {α : Type}
    (value : α) (values : List α) :
    FiniteMatch.ofList (value :: values) =
      FiniteMatch.add value (FiniteMatch.ofList values) := by
  cases values with
  | nil => rfl
  | cons head tail => cases tail <;> rfl

def encodeDocumentCount : FiniteMatch SourceDocument → Pattern
  | .none => documentNone
  | .one document => documentOne (Carrier.encodeSourceDocument document)
  | .many => documentMany

def encodeBindingCount : FiniteMatch IncludeBinding → Pattern
  | .none => bindingNone
  | .one binding => bindingOne (Carrier.encodeIncludeBinding binding)
  | .many => bindingMany

def documentMatches (canonicalId : String)
    (documents : List SourceDocument) : List SourceDocument :=
  documents.filter fun document => document.canonicalId = canonicalId

def bindingMatches (fromSource requestedFile : String)
    (bindings : List IncludeBinding) : List IncludeBinding :=
  bindings.filter fun binding =>
    binding.fromSource = fromSource && binding.requestedFile = requestedFile

def documentOutcome (canonicalId : String) :
    FiniteMatch SourceDocument → Except ResolutionError SourceDocument
  | .none => .error (.missingDocument canonicalId)
  | .one document => .ok document
  | .many => .error (.ambiguousDocument canonicalId)

def bindingOutcome (fromSource requestedFile : String) :
    FiniteMatch IncludeBinding → Except ResolutionError IncludeBinding
  | .none => .error (.missingBinding fromSource requestedFile)
  | .one binding => .ok binding
  | .many => .error (.ambiguousBinding fromSource requestedFile)

theorem documentOutcome_classification_eq_lookupDocument
    (environment : SourceEnvironment) (canonicalId : String) :
    documentOutcome canonicalId
        (FiniteMatch.ofList (documentMatches canonicalId environment.documents)) =
      TptpOfficialIncludeResolution.lookupDocument environment canonicalId := by
  simp only [documentMatches, TptpOfficialIncludeResolution.lookupDocument,
    TptpOfficialIncludeResolution.documentsNamed]
  cases environment.documents.filter
      (fun document => document.canonicalId = canonicalId) with
  | nil => rfl
  | cons head tail => cases tail <;> rfl

theorem bindingOutcome_classification_eq_lookupBinding
    (environment : SourceEnvironment) (fromSource requestedFile : String) :
    bindingOutcome fromSource requestedFile
        (FiniteMatch.ofList
          (bindingMatches fromSource requestedFile environment.bindings)) =
      TptpOfficialIncludeResolution.lookupBinding environment
        fromSource requestedFile := by
  simp only [bindingMatches, TptpOfficialIncludeResolution.lookupBinding,
    TptpOfficialIncludeResolution.bindingsFor]
  cases environment.bindings.filter
      (fun binding =>
        binding.fromSource = fromSource &&
          binding.requestedFile = requestedFile) with
  | nil => rfl
  | cons head tail => cases tail <;> rfl

private abbrev base : BasePremiseEvaluator :=
  engineBasePremises relations

/-- Exact singleton results are stable above a finite contextual depth. -/
def EventuallyExact (source result : Pattern) : Prop :=
  ∃ requiredFuel, ∀ fuel, requiredFuel ≤ fuel →
    rewriteAt base language fuel source = [result]

private theorem eventuallyExact_of_one_step (source result : Pattern)
    (step : ∀ fuel, rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  refine ⟨1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor

private theorem eventuallyExact_of_one_premise
    (premiseSource premiseResult source result : Pattern)
    (premiseExact : EventuallyExact premiseSource premiseResult)
    (step : ∀ fuel,
      rewriteAt base language fuel premiseSource = [premiseResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases premiseExact with ⟨requiredFuel, premiseExact⟩
  refine ⟨requiredFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using
        step predecessor (premiseExact predecessor (by omega))

private theorem eventuallyExact_of_two_premises
    (firstSource firstResult secondSource secondResult source result : Pattern)
    (firstExact : EventuallyExact firstSource firstResult)
    (secondExact : EventuallyExact secondSource secondResult)
    (step : ∀ fuel,
      rewriteAt base language fuel firstSource = [firstResult] →
      rewriteAt base language fuel secondSource = [secondResult] →
        rewriteAt base language (fuel + 1) source = [result]) :
    EventuallyExact source result := by
  rcases firstExact with ⟨firstFuel, firstExact⟩
  rcases secondExact with ⟨secondFuel, secondExact⟩
  refine ⟨max firstFuel secondFuel + 1, ?_⟩
  intro fuel enough
  cases fuel with
  | zero => simp at enough
  | succ predecessor =>
      simpa [Nat.succ_eq_add_one] using step predecessor
        (firstExact predecessor (by omega))
        (secondExact predecessor (by omega))

private theorem encodeString_injective : Function.Injective Carrier.encodeString := by
  intro left right equalEncoding
  have decoded := congrArg
    TptpOfficialIncludeResolutionCarrier.decodeString? equalEncoding
  simpa using decoded

private theorem documentLookupRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:lookup-document") =
      [documentRules.get ⟨0, by decide⟩] := by
  rfl

private theorem scanDocumentsRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:scan-documents") =
      [documentRules.get ⟨1, by decide⟩,
       documentRules.get ⟨2, by decide⟩] := by
  rfl

private theorem documentDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:document-decision") =
      [documentRules.get ⟨3, by decide⟩,
       documentRules.get ⟨4, by decide⟩,
       documentRules.get ⟨5, by decide⟩,
       documentRules.get ⟨6, by decide⟩] := by
  rfl

private theorem finishDocumentRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:finish-document") =
      [documentRules.get ⟨7, by decide⟩,
       documentRules.get ⟨8, by decide⟩,
       documentRules.get ⟨9, by decide⟩] := by
  rfl

private theorem bindingLookupRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:lookup-binding") =
      [bindingRules.get ⟨0, by decide⟩] := by
  rfl

private theorem scanBindingsRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:scan-bindings") =
      [bindingRules.get ⟨1, by decide⟩,
       bindingRules.get ⟨2, by decide⟩] := by
  rfl

private theorem bindingFromDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:binding-from-decision") =
      [bindingRules.get ⟨3, by decide⟩,
       bindingRules.get ⟨4, by decide⟩] := by
  rfl

private theorem bindingRequestDecisionRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:binding-request-decision") =
      [bindingRules.get ⟨5, by decide⟩,
       bindingRules.get ⟨6, by decide⟩,
       bindingRules.get ⟨7, by decide⟩,
       bindingRules.get ⟨8, by decide⟩] := by
  rfl

private theorem finishBindingRootRules :
    language.rewrites.filter
        (rootMatches "tptp-include-lookup:finish-binding") =
      [bindingRules.get ⟨9, by decide⟩,
       bindingRules.get ⟨10, by decide⟩,
       bindingRules.get ⟨11, by decide⟩] := by
  rfl

local macro "lookup_row_simp" : tactic =>
  `(tactic|
    simp [documentRules, bindingRules,
      sourceEnvironment, sourceDocumentsNil, sourceDocumentsCons,
      sourceDocument, includeBindingsNil, includeBindingsCons, includeBinding,
      errorMissingDocument, errorAmbiguousDocument,
      errorMissingBinding, errorAmbiguousBinding,
      documentNone, documentOne, documentMany,
      bindingNone, bindingOne, bindingMany,
      documentOk, documentError, bindingOk, bindingError,
      TptpOfficialIncludeEnvironmentLookupLanguageDef.lookupDocument,
      scanDocuments, documentDecision, finishDocument,
      TptpOfficialIncludeEnvironmentLookupLanguageDef.lookupBinding,
      scanBindings, bindingFromDecision,
      bindingRequestDecision, finishBinding,
      mkRule, congruence, typed, a, v, applyRuleUsing,
      matchPatternForRule_eq_syntactic, premisesUsing, premiseStepUsing,
      matchPattern, matchArgs, mergeBindings, applyBindingsForRule,
      applyBindings, PatternEqualityDecision.equal,
      PatternEqualityDecision.different,
      TptpOfficialIncludeResolutionResultCarrier.encodeResolutionError,
      TptpOfficialIncludeResolutionResultCarrier.encodeString,
      TptpOfficialIncludeResolutionCarrier.encodeString,
      Carrier.encodeString, Carrier.encodeResolutionError,
      encodeResolutionError_missingDocument,
      encodeResolutionError_ambiguousDocument,
      encodeResolutionError_missingBinding,
      encodeResolutionError_ambiguousBinding])

private theorem equalityPremise_equal_exact
    (left tailDocument officialFile digest : Pattern) :
    base language
        [("documentId", left), ("officialFile", officialFile),
         ("digest", digest), ("documents", tailDocument),
         ("canonicalId", left)]
        (.relationQuery PatternEqualityDecision.relationName
          [v "canonicalId", v "documentId", v "decision"]) =
      [[("decision", PatternEqualityDecision.equal),
        ("documentId", left), ("officialFile", officialFile),
        ("digest", digest), ("documents", tailDocument),
        ("canonicalId", left)]] := by
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings, v]

private theorem equalityPremise_different_exact
    (left right tailDocument officialFile digest : Pattern)
    (different : left ≠ right) :
    base language
        [("documentId", right), ("officialFile", officialFile),
         ("digest", digest), ("documents", tailDocument),
         ("canonicalId", left)]
        (.relationQuery PatternEqualityDecision.relationName
          [v "canonicalId", v "documentId", v "decision"]) =
      [[("decision", PatternEqualityDecision.different),
        ("documentId", right), ("officialFile", officialFile),
        ("digest", digest), ("documents", tailDocument),
        ("canonicalId", left)]] := by
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings,
    v, different]

theorem scanDocuments_nil_rewriteAt_exact (fuel : Nat)
    (canonicalId : Pattern) :
    rewriteAt base language (fuel + 1)
      (scanDocuments canonicalId sourceDocumentsNil) = [documentNone] := by
  simp only [scanDocuments, sourceDocumentsNil, a]
  rw [rewriteAt_eq_root_filter, scanDocumentsRootRules]
  lookup_row_simp

theorem documentDecision_different_rewriteAt_exact (fuel : Nat)
    (document tail : Pattern) :
    rewriteAt base language (fuel + 1)
      (documentDecision PatternEqualityDecision.different document tail) =
      [tail] := by
  simp only [documentDecision, a]
  rw [rewriteAt_eq_root_filter, documentDecisionRootRules]
  lookup_row_simp

theorem documentDecision_equal_rewriteAt_exact (fuel : Nat)
    (document : Pattern) (count : FiniteMatch SourceDocument) :
    rewriteAt base language (fuel + 1)
        (documentDecision PatternEqualityDecision.equal document
          (encodeDocumentCount count)) =
      [match count with
       | .none => documentOne document
       | .one _ => documentMany
       | .many => documentMany] := by
  cases count <;> simp only [encodeDocumentCount, documentDecision, a] <;>
    rw [rewriteAt_eq_root_filter, documentDecisionRootRules] <;>
    lookup_row_simp

theorem finishDocument_rewriteAt_exact (fuel : Nat)
    (canonicalId : String) (count : FiniteMatch SourceDocument) :
    rewriteAt base language (fuel + 1)
        (finishDocument (Carrier.encodeString canonicalId)
          (encodeDocumentCount count)) =
      [encodeDocumentOutcome (documentOutcome canonicalId count)] := by
  cases count <;> simp only [encodeDocumentCount, encodeDocumentOutcome,
      documentOutcome, finishDocument, a] <;>
    rw [rewriteAt_eq_root_filter, finishDocumentRootRules] <;>
    lookup_row_simp

theorem scanDocuments_cons_equal_rewriteAt_exact (fuel : Nat)
    (canonicalId digest officialFile documents tail result : Pattern)
    (scanTail :
      rewriteAt base language fuel
          (scanDocuments canonicalId documents) = [tail])
    (finishHead :
      rewriteAt base language fuel
          (documentDecision PatternEqualityDecision.equal
            (sourceDocument canonicalId digest officialFile) tail) = [result]) :
    rewriteAt base language (fuel + 1)
        (scanDocuments canonicalId
          (sourceDocumentsCons
            (sourceDocument canonicalId digest officialFile) documents)) =
      [result] := by
  simp only [scanDocuments, documentDecision, sourceDocument, a]
    at scanTail finishHead
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:scan-documents"
      [canonicalId,
       .apply "tptp-include-resolution:source-documents-cons"
        [.apply "tptp-include-resolution:source-document"
          [canonicalId, digest, officialFile], documents]]) = [result]
  rw [rewriteAt_eq_root_filter, scanDocumentsRootRules]
  lookup_row_simp
  have relationStep := equalityPremise_equal_exact
    canonicalId documents officialFile digest
  simp only [v] at relationStep
  rw [relationStep]
  simp
  rw [scanTail]
  simp
  rw [finishHead]
  simp

theorem scanDocuments_cons_different_rewriteAt_exact (fuel : Nat)
    (canonicalId documentId digest officialFile documents tail result : Pattern)
    (different : canonicalId ≠ documentId)
    (scanTail :
      rewriteAt base language fuel
          (scanDocuments canonicalId documents) = [tail])
    (finishHead :
      rewriteAt base language fuel
          (documentDecision PatternEqualityDecision.different
            (sourceDocument documentId digest officialFile) tail) = [result]) :
    rewriteAt base language (fuel + 1)
        (scanDocuments canonicalId
          (sourceDocumentsCons
            (sourceDocument documentId digest officialFile) documents)) =
      [result] := by
  simp only [scanDocuments, documentDecision, sourceDocument, a]
    at scanTail finishHead
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:scan-documents"
      [canonicalId,
       .apply "tptp-include-resolution:source-documents-cons"
        [.apply "tptp-include-resolution:source-document"
          [documentId, digest, officialFile], documents]]) = [result]
  rw [rewriteAt_eq_root_filter, scanDocumentsRootRules]
  lookup_row_simp
  have relationStep := equalityPremise_different_exact
    canonicalId documentId documents officialFile digest different
  simp only [v] at relationStep
  rw [relationStep]
  simp
  rw [scanTail]
  simp
  rw [finishHead]
  simp

theorem scanDocuments_encode_eventuallyExact (canonicalId : String) :
    ∀ documents : List SourceDocument,
      EventuallyExact
        (scanDocuments (Carrier.encodeString canonicalId)
          (Carrier.encodeSourceDocuments documents))
        (encodeDocumentCount
          (FiniteMatch.ofList (documentMatches canonicalId documents))) := by
  intro documents
  induction documents with
  | nil =>
      simp only [Carrier.encodeSourceDocuments, documentMatches,
        List.filter_nil, FiniteMatch.ofList, encodeDocumentCount]
      apply eventuallyExact_of_one_step
      intro fuel
      exact scanDocuments_nil_rewriteAt_exact fuel
        (Carrier.encodeString canonicalId)
  | cons document documents inductionHypothesis =>
      rcases document with ⟨documentId, digest, officialFile⟩
      by_cases sameId : canonicalId = documentId
      · subst documentId
        let tailCount := FiniteMatch.ofList
          (documentMatches canonicalId documents)
        have decisionExact : EventuallyExact
            (documentDecision PatternEqualityDecision.equal
              (sourceDocument (Carrier.encodeString canonicalId)
                (Carrier.encodeString digest) officialFile)
              (encodeDocumentCount tailCount))
            (encodeDocumentCount
              (FiniteMatch.add
                { canonicalId := canonicalId, digest, officialFile }
                tailCount)) := by
          cases tailCount with
          | none =>
              apply eventuallyExact_of_one_step
              intro fuel
              simpa [FiniteMatch.add, encodeDocumentCount,
                encodeSourceDocument_eq] using
                documentDecision_equal_rewriteAt_exact fuel
                  (sourceDocument (Carrier.encodeString canonicalId)
                    (Carrier.encodeString digest) officialFile)
                  (FiniteMatch.none : FiniteMatch SourceDocument)
          | one existing =>
              apply eventuallyExact_of_one_step
              intro fuel
              simpa [FiniteMatch.add, encodeDocumentCount] using
                documentDecision_equal_rewriteAt_exact fuel
                  (sourceDocument (Carrier.encodeString canonicalId)
                    (Carrier.encodeString digest) officialFile)
                  (FiniteMatch.one existing)
          | many =>
              apply eventuallyExact_of_one_step
              intro fuel
              simpa [FiniteMatch.add, encodeDocumentCount] using
                documentDecision_equal_rewriteAt_exact fuel
                  (sourceDocument (Carrier.encodeString canonicalId)
                    (Carrier.encodeString digest) officialFile)
                  (FiniteMatch.many : FiniteMatch SourceDocument)
        have composed := eventuallyExact_of_two_premises
          (scanDocuments (Carrier.encodeString canonicalId)
            (Carrier.encodeSourceDocuments documents))
          (encodeDocumentCount tailCount)
          (documentDecision PatternEqualityDecision.equal
            (sourceDocument (Carrier.encodeString canonicalId)
              (Carrier.encodeString digest) officialFile)
            (encodeDocumentCount tailCount))
          (encodeDocumentCount
            (FiniteMatch.add
              { canonicalId := canonicalId, digest, officialFile }
              tailCount))
          (scanDocuments (Carrier.encodeString canonicalId)
            (sourceDocumentsCons
              (sourceDocument (Carrier.encodeString canonicalId)
                (Carrier.encodeString digest) officialFile)
              (Carrier.encodeSourceDocuments documents)))
          (encodeDocumentCount
            (FiniteMatch.add
              { canonicalId := canonicalId, digest, officialFile }
              tailCount))
          inductionHypothesis decisionExact
          (fun fuel scanTail finishHead =>
            scanDocuments_cons_equal_rewriteAt_exact fuel
              (Carrier.encodeString canonicalId) (Carrier.encodeString digest)
              officialFile (Carrier.encodeSourceDocuments documents)
              (encodeDocumentCount tailCount)
              (encodeDocumentCount
                (FiniteMatch.add
                  { canonicalId := canonicalId, digest, officialFile }
                  tailCount))
              scanTail finishHead)
        simpa [documentMatches, tailCount, encodeSourceDocument_eq] using composed
      · have differentId : documentId ≠ canonicalId := Ne.symm sameId
        have differentEncoding :
            Carrier.encodeString canonicalId ≠
              Carrier.encodeString documentId := by
          intro equalEncoding
          exact sameId (encodeString_injective equalEncoding)
        let tailCount := FiniteMatch.ofList
          (documentMatches canonicalId documents)
        have decisionExact : EventuallyExact
            (documentDecision PatternEqualityDecision.different
              (sourceDocument (Carrier.encodeString documentId)
                (Carrier.encodeString digest) officialFile)
              (encodeDocumentCount tailCount))
            (encodeDocumentCount tailCount) := by
          apply eventuallyExact_of_one_step
          intro fuel
          exact documentDecision_different_rewriteAt_exact fuel
            (sourceDocument (Carrier.encodeString documentId)
              (Carrier.encodeString digest) officialFile)
            (encodeDocumentCount tailCount)
        have composed := eventuallyExact_of_two_premises
          (scanDocuments (Carrier.encodeString canonicalId)
            (Carrier.encodeSourceDocuments documents))
          (encodeDocumentCount tailCount)
          (documentDecision PatternEqualityDecision.different
            (sourceDocument (Carrier.encodeString documentId)
              (Carrier.encodeString digest) officialFile)
            (encodeDocumentCount tailCount))
          (encodeDocumentCount tailCount)
          (scanDocuments (Carrier.encodeString canonicalId)
            (sourceDocumentsCons
              (sourceDocument (Carrier.encodeString documentId)
                (Carrier.encodeString digest) officialFile)
              (Carrier.encodeSourceDocuments documents)))
          (encodeDocumentCount tailCount)
          inductionHypothesis decisionExact
          (fun fuel scanTail finishHead =>
            scanDocuments_cons_different_rewriteAt_exact fuel
              (Carrier.encodeString canonicalId)
              (Carrier.encodeString documentId)
              (Carrier.encodeString digest) officialFile
              (Carrier.encodeSourceDocuments documents)
              (encodeDocumentCount tailCount) (encodeDocumentCount tailCount)
              differentEncoding scanTail finishHead)
        simpa [documentMatches, tailCount, differentId,
          encodeSourceDocument_eq] using composed

theorem lookupDocument_rewriteAt_exact (fuel : Nat)
    (canonicalId documents bindings count result : Pattern)
    (scanStep :
      rewriteAt base language fuel
          (scanDocuments canonicalId documents) = [count])
    (finishStep :
      rewriteAt base language fuel
          (finishDocument canonicalId count) = [result]) :
    rewriteAt base language (fuel + 1)
        (TptpOfficialIncludeEnvironmentLookupLanguageDef.lookupDocument
          canonicalId (sourceEnvironment documents bindings)) = [result] := by
  simp only [scanDocuments, finishDocument, a] at scanStep finishStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:lookup-document"
      [canonicalId,
       .apply "tptp-include-resolution:source-environment"
        [documents, bindings]]) = [result]
  rw [rewriteAt_eq_root_filter, documentLookupRootRules]
  lookup_row_simp
  rw [scanStep]
  simp
  rw [finishStep]
  simp

theorem lookupDocument_encode_eventuallyExact
    (environment : SourceEnvironment) (canonicalId : String) :
    EventuallyExact (encodeDocumentRequest environment canonicalId)
      (encodeDocumentOutcome
        (TptpOfficialIncludeResolution.lookupDocument environment canonicalId)) := by
  let count := FiniteMatch.ofList
    (documentMatches canonicalId environment.documents)
  have scanExact := scanDocuments_encode_eventuallyExact
    canonicalId environment.documents
  have finishExact : EventuallyExact
      (finishDocument (Carrier.encodeString canonicalId)
        (encodeDocumentCount count))
      (encodeDocumentOutcome (documentOutcome canonicalId count)) := by
    apply eventuallyExact_of_one_step
    intro fuel
    exact finishDocument_rewriteAt_exact fuel canonicalId count
  have composed := eventuallyExact_of_two_premises
    (scanDocuments (Carrier.encodeString canonicalId)
      (Carrier.encodeSourceDocuments environment.documents))
    (encodeDocumentCount count)
    (finishDocument (Carrier.encodeString canonicalId)
      (encodeDocumentCount count))
    (encodeDocumentOutcome (documentOutcome canonicalId count))
    (encodeDocumentRequest environment canonicalId)
    (encodeDocumentOutcome (documentOutcome canonicalId count))
    scanExact finishExact
    (fun fuel scanStep finishStep =>
      lookupDocument_rewriteAt_exact fuel
        (Carrier.encodeString canonicalId)
        (Carrier.encodeSourceDocuments environment.documents)
        (Carrier.encodeIncludeBindings environment.bindings)
        (encodeDocumentCount count)
        (encodeDocumentOutcome (documentOutcome canonicalId count))
        scanStep finishStep)
  rw [documentOutcome_classification_eq_lookupDocument] at composed
  exact composed

theorem scanBindings_nil_rewriteAt_exact (fuel : Nat)
    (fromSource requestedFile : Pattern) :
    rewriteAt base language (fuel + 1)
        (scanBindings fromSource requestedFile includeBindingsNil) =
      [bindingNone] := by
  simp only [scanBindings, includeBindingsNil, a]
  rw [rewriteAt_eq_root_filter, scanBindingsRootRules]
  lookup_row_simp

theorem bindingFromDecision_different_rewriteAt_exact (fuel : Nat)
    (requestedFile binding tail : Pattern) :
    rewriteAt base language (fuel + 1)
        (bindingFromDecision PatternEqualityDecision.different
          requestedFile binding tail) = [tail] := by
  simp only [bindingFromDecision, a]
  rw [rewriteAt_eq_root_filter, bindingFromDecisionRootRules]
  lookup_row_simp

theorem bindingRequestDecision_different_rewriteAt_exact (fuel : Nat)
    (binding tail : Pattern) :
    rewriteAt base language (fuel + 1)
        (bindingRequestDecision PatternEqualityDecision.different binding tail) =
      [tail] := by
  simp only [bindingRequestDecision, a]
  rw [rewriteAt_eq_root_filter, bindingRequestDecisionRootRules]
  lookup_row_simp

theorem bindingRequestDecision_equal_rewriteAt_exact (fuel : Nat)
    (binding : Pattern) (count : FiniteMatch IncludeBinding) :
    rewriteAt base language (fuel + 1)
        (bindingRequestDecision PatternEqualityDecision.equal binding
          (encodeBindingCount count)) =
      [match count with
       | .none => bindingOne binding
       | .one _ => bindingMany
       | .many => bindingMany] := by
  cases count <;> simp only [encodeBindingCount, bindingRequestDecision, a] <;>
    rw [rewriteAt_eq_root_filter, bindingRequestDecisionRootRules] <;>
    lookup_row_simp

theorem bindingFromDecision_equal_equal_rewriteAt_exact (fuel : Nat)
    (fromSource requestedFile targetSource tail result : Pattern)
    (decisionStep :
      rewriteAt base language fuel
          (bindingRequestDecision PatternEqualityDecision.equal
            (includeBinding fromSource requestedFile targetSource) tail) =
        [result]) :
    rewriteAt base language (fuel + 1)
        (bindingFromDecision PatternEqualityDecision.equal requestedFile
          (includeBinding fromSource requestedFile targetSource) tail) =
      [result] := by
  simp only [bindingRequestDecision, includeBinding, a] at decisionStep
  simp only [base, relations, PatternEqualityDecision.relationEnv]
    at decisionStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:binding-from-decision"
      [PatternEqualityDecision.equal, requestedFile,
       .apply "tptp-include-resolution:include-binding"
        [fromSource, requestedFile, targetSource], tail]) = [result]
  rw [rewriteAt_eq_root_filter, bindingFromDecisionRootRules]
  lookup_row_simp
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings]
  rw [decisionStep]
  simp

theorem bindingFromDecision_equal_different_rewriteAt_exact (fuel : Nat)
    (requestedFile bindingFrom bindingRequested targetSource tail result : Pattern)
    (different : requestedFile ≠ bindingRequested)
    (decisionStep :
      rewriteAt base language fuel
          (bindingRequestDecision PatternEqualityDecision.different
            (includeBinding bindingFrom bindingRequested targetSource) tail) =
        [result]) :
    rewriteAt base language (fuel + 1)
        (bindingFromDecision PatternEqualityDecision.equal requestedFile
          (includeBinding bindingFrom bindingRequested targetSource) tail) =
      [result] := by
  simp only [bindingRequestDecision, includeBinding, a] at decisionStep
  simp only [base, relations, PatternEqualityDecision.relationEnv]
    at decisionStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:binding-from-decision"
      [PatternEqualityDecision.equal, requestedFile,
       .apply "tptp-include-resolution:include-binding"
        [bindingFrom, bindingRequested, targetSource], tail]) = [result]
  rw [rewriteAt_eq_root_filter, bindingFromDecisionRootRules]
  lookup_row_simp
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings,
    different]
  rw [decisionStep]
  simp

theorem scanBindings_cons_equal_rewriteAt_exact (fuel : Nat)
    (fromSource requestedFile bindingRequested targetSource bindings
      tail result : Pattern)
    (scanTail :
      rewriteAt base language fuel
          (scanBindings fromSource requestedFile bindings) = [tail])
    (finishHead :
      rewriteAt base language fuel
          (bindingFromDecision PatternEqualityDecision.equal requestedFile
            (includeBinding fromSource bindingRequested targetSource) tail) =
        [result]) :
    rewriteAt base language (fuel + 1)
        (scanBindings fromSource requestedFile
          (includeBindingsCons
            (includeBinding fromSource bindingRequested targetSource)
            bindings)) = [result] := by
  simp only [scanBindings, bindingFromDecision, includeBinding, a]
    at scanTail finishHead
  simp only [base, relations, PatternEqualityDecision.relationEnv]
    at scanTail finishHead
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:scan-bindings"
      [fromSource, requestedFile,
       .apply "tptp-include-resolution:include-bindings-cons"
        [.apply "tptp-include-resolution:include-binding"
          [fromSource, bindingRequested, targetSource], bindings]]) = [result]
  rw [rewriteAt_eq_root_filter, scanBindingsRootRules]
  lookup_row_simp
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings]
  rw [scanTail]
  simp
  rw [finishHead]
  simp

theorem scanBindings_cons_different_rewriteAt_exact (fuel : Nat)
    (fromSource requestedFile bindingFrom bindingRequested targetSource
      bindings tail result : Pattern)
    (different : fromSource ≠ bindingFrom)
    (scanTail :
      rewriteAt base language fuel
          (scanBindings fromSource requestedFile bindings) = [tail])
    (finishHead :
      rewriteAt base language fuel
          (bindingFromDecision PatternEqualityDecision.different requestedFile
            (includeBinding bindingFrom bindingRequested targetSource) tail) =
        [result]) :
    rewriteAt base language (fuel + 1)
        (scanBindings fromSource requestedFile
          (includeBindingsCons
            (includeBinding bindingFrom bindingRequested targetSource)
            bindings)) = [result] := by
  simp only [scanBindings, bindingFromDecision, includeBinding, a]
    at scanTail finishHead
  simp only [base, relations, PatternEqualityDecision.relationEnv]
    at scanTail finishHead
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:scan-bindings"
      [fromSource, requestedFile,
       .apply "tptp-include-resolution:include-bindings-cons"
        [.apply "tptp-include-resolution:include-binding"
          [bindingFrom, bindingRequested, targetSource], bindings]]) = [result]
  rw [rewriteAt_eq_root_filter, scanBindingsRootRules]
  lookup_row_simp
  simp [base, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, relations, PatternEqualityDecision.relationEnv,
    PatternEqualityDecision.relationName,
    PatternEqualityDecision.relationTuples, matchRelationArgs,
    matchRelationArgument, Bindings.lookup, mergeBindings, applyBindings,
    different]
  rw [scanTail]
  simp
  rw [finishHead]
  simp

theorem finishBinding_rewriteAt_exact (fuel : Nat)
    (fromSource requestedFile : String) (count : FiniteMatch IncludeBinding) :
    rewriteAt base language (fuel + 1)
        (finishBinding (Carrier.encodeString fromSource)
          (Carrier.encodeString requestedFile) (encodeBindingCount count)) =
      [encodeBindingOutcome
        (bindingOutcome fromSource requestedFile count)] := by
  cases count <;> simp only [encodeBindingCount, encodeBindingOutcome,
      bindingOutcome, finishBinding, a] <;>
    rw [rewriteAt_eq_root_filter, finishBindingRootRules] <;>
    lookup_row_simp

theorem scanBindings_encode_eventuallyExact
    (fromSource requestedFile : String) :
    ∀ bindings : List IncludeBinding,
      EventuallyExact
        (scanBindings (Carrier.encodeString fromSource)
          (Carrier.encodeString requestedFile)
          (Carrier.encodeIncludeBindings bindings))
        (encodeBindingCount
          (FiniteMatch.ofList
            (bindingMatches fromSource requestedFile bindings))) := by
  intro bindings
  induction bindings with
  | nil =>
      simp only [Carrier.encodeIncludeBindings, bindingMatches,
        List.filter_nil, FiniteMatch.ofList, encodeBindingCount]
      apply eventuallyExact_of_one_step
      intro fuel
      exact scanBindings_nil_rewriteAt_exact fuel
        (Carrier.encodeString fromSource) (Carrier.encodeString requestedFile)
  | cons binding bindings inductionHypothesis =>
      rcases binding with ⟨bindingFrom, bindingRequested, targetSource⟩
      by_cases sameFrom : fromSource = bindingFrom
      · subst bindingFrom
        by_cases sameRequest : requestedFile = bindingRequested
        · subst bindingRequested
          let tailCount := FiniteMatch.ofList
            (bindingMatches fromSource requestedFile bindings)
          have requestDecisionExact : EventuallyExact
              (bindingRequestDecision PatternEqualityDecision.equal
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString requestedFile)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount
                (FiniteMatch.add
                  { fromSource, requestedFile, targetSource } tailCount)) := by
            cases tailCount with
            | none =>
                apply eventuallyExact_of_one_step
                intro fuel
                simpa [FiniteMatch.add, encodeBindingCount,
                  encodeIncludeBinding_eq] using
                  bindingRequestDecision_equal_rewriteAt_exact fuel
                    (includeBinding (Carrier.encodeString fromSource)
                      (Carrier.encodeString requestedFile)
                      (Carrier.encodeString targetSource))
                    (FiniteMatch.none : FiniteMatch IncludeBinding)
            | one existing =>
                apply eventuallyExact_of_one_step
                intro fuel
                simpa [FiniteMatch.add, encodeBindingCount] using
                  bindingRequestDecision_equal_rewriteAt_exact fuel
                    (includeBinding (Carrier.encodeString fromSource)
                      (Carrier.encodeString requestedFile)
                      (Carrier.encodeString targetSource))
                    (FiniteMatch.one existing)
            | many =>
                apply eventuallyExact_of_one_step
                intro fuel
                simpa [FiniteMatch.add, encodeBindingCount] using
                  bindingRequestDecision_equal_rewriteAt_exact fuel
                    (includeBinding (Carrier.encodeString fromSource)
                      (Carrier.encodeString requestedFile)
                      (Carrier.encodeString targetSource))
                    (FiniteMatch.many : FiniteMatch IncludeBinding)
          have fromDecisionExact : EventuallyExact
              (bindingFromDecision PatternEqualityDecision.equal
                (Carrier.encodeString requestedFile)
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString requestedFile)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount
                (FiniteMatch.add
                  { fromSource, requestedFile, targetSource } tailCount)) := by
            apply eventuallyExact_of_one_premise
              (bindingRequestDecision PatternEqualityDecision.equal
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString requestedFile)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount
                (FiniteMatch.add
                  { fromSource, requestedFile, targetSource } tailCount))
              (bindingFromDecision PatternEqualityDecision.equal
                (Carrier.encodeString requestedFile)
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString requestedFile)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount
                (FiniteMatch.add
                  { fromSource, requestedFile, targetSource } tailCount))
              requestDecisionExact
            intro fuel decisionStep
            exact bindingFromDecision_equal_equal_rewriteAt_exact fuel
              (Carrier.encodeString fromSource)
              (Carrier.encodeString requestedFile)
              (Carrier.encodeString targetSource)
              (encodeBindingCount tailCount)
              (encodeBindingCount
                (FiniteMatch.add
                  { fromSource, requestedFile, targetSource } tailCount))
              decisionStep
          have composed := eventuallyExact_of_two_premises
            (scanBindings (Carrier.encodeString fromSource)
              (Carrier.encodeString requestedFile)
              (Carrier.encodeIncludeBindings bindings))
            (encodeBindingCount tailCount)
            (bindingFromDecision PatternEqualityDecision.equal
              (Carrier.encodeString requestedFile)
              (includeBinding (Carrier.encodeString fromSource)
                (Carrier.encodeString requestedFile)
                (Carrier.encodeString targetSource))
              (encodeBindingCount tailCount))
            (encodeBindingCount
              (FiniteMatch.add
                { fromSource, requestedFile, targetSource } tailCount))
            (scanBindings (Carrier.encodeString fromSource)
              (Carrier.encodeString requestedFile)
              (includeBindingsCons
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString requestedFile)
                  (Carrier.encodeString targetSource))
                (Carrier.encodeIncludeBindings bindings)))
            (encodeBindingCount
              (FiniteMatch.add
                { fromSource, requestedFile, targetSource } tailCount))
            inductionHypothesis fromDecisionExact
            (fun fuel scanTail finishHead =>
              scanBindings_cons_equal_rewriteAt_exact fuel
                (Carrier.encodeString fromSource)
                (Carrier.encodeString requestedFile)
                (Carrier.encodeString requestedFile)
                (Carrier.encodeString targetSource)
                (Carrier.encodeIncludeBindings bindings)
                (encodeBindingCount tailCount)
                (encodeBindingCount
                  (FiniteMatch.add
                    { fromSource, requestedFile, targetSource } tailCount))
                scanTail finishHead)
          simpa [bindingMatches, tailCount, encodeIncludeBinding_eq] using
            composed
        · have differentRequested : bindingRequested ≠ requestedFile :=
            Ne.symm sameRequest
          have differentRequestEncoding :
              Carrier.encodeString requestedFile ≠
                Carrier.encodeString bindingRequested := by
            intro equalEncoding
            exact sameRequest (encodeString_injective equalEncoding)
          let tailCount := FiniteMatch.ofList
            (bindingMatches fromSource requestedFile bindings)
          have requestDecisionExact : EventuallyExact
              (bindingRequestDecision PatternEqualityDecision.different
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString bindingRequested)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount tailCount) := by
            apply eventuallyExact_of_one_step
            intro fuel
            exact bindingRequestDecision_different_rewriteAt_exact fuel
              (includeBinding (Carrier.encodeString fromSource)
                (Carrier.encodeString bindingRequested)
                (Carrier.encodeString targetSource))
              (encodeBindingCount tailCount)
          have fromDecisionExact : EventuallyExact
              (bindingFromDecision PatternEqualityDecision.equal
                (Carrier.encodeString requestedFile)
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString bindingRequested)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount tailCount) := by
            apply eventuallyExact_of_one_premise
              (bindingRequestDecision PatternEqualityDecision.different
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString bindingRequested)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount tailCount)
              (bindingFromDecision PatternEqualityDecision.equal
                (Carrier.encodeString requestedFile)
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString bindingRequested)
                  (Carrier.encodeString targetSource))
                (encodeBindingCount tailCount))
              (encodeBindingCount tailCount)
              requestDecisionExact
            intro fuel decisionStep
            exact bindingFromDecision_equal_different_rewriteAt_exact fuel
              (Carrier.encodeString requestedFile)
              (Carrier.encodeString fromSource)
              (Carrier.encodeString bindingRequested)
              (Carrier.encodeString targetSource)
              (encodeBindingCount tailCount) (encodeBindingCount tailCount)
              differentRequestEncoding decisionStep
          have composed := eventuallyExact_of_two_premises
            (scanBindings (Carrier.encodeString fromSource)
              (Carrier.encodeString requestedFile)
              (Carrier.encodeIncludeBindings bindings))
            (encodeBindingCount tailCount)
            (bindingFromDecision PatternEqualityDecision.equal
              (Carrier.encodeString requestedFile)
              (includeBinding (Carrier.encodeString fromSource)
                (Carrier.encodeString bindingRequested)
                (Carrier.encodeString targetSource))
              (encodeBindingCount tailCount))
            (encodeBindingCount tailCount)
            (scanBindings (Carrier.encodeString fromSource)
              (Carrier.encodeString requestedFile)
              (includeBindingsCons
                (includeBinding (Carrier.encodeString fromSource)
                  (Carrier.encodeString bindingRequested)
                  (Carrier.encodeString targetSource))
                (Carrier.encodeIncludeBindings bindings)))
            (encodeBindingCount tailCount)
            inductionHypothesis fromDecisionExact
            (fun fuel scanTail finishHead =>
              scanBindings_cons_equal_rewriteAt_exact fuel
                (Carrier.encodeString fromSource)
                (Carrier.encodeString requestedFile)
                (Carrier.encodeString bindingRequested)
                (Carrier.encodeString targetSource)
                (Carrier.encodeIncludeBindings bindings)
                (encodeBindingCount tailCount) (encodeBindingCount tailCount)
                scanTail finishHead)
          simpa [bindingMatches, tailCount, differentRequested,
            encodeIncludeBinding_eq] using composed
      · have differentFrom : bindingFrom ≠ fromSource := Ne.symm sameFrom
        have differentFromEncoding :
            Carrier.encodeString fromSource ≠
              Carrier.encodeString bindingFrom := by
          intro equalEncoding
          exact sameFrom (encodeString_injective equalEncoding)
        let tailCount := FiniteMatch.ofList
          (bindingMatches fromSource requestedFile bindings)
        have fromDecisionExact : EventuallyExact
            (bindingFromDecision PatternEqualityDecision.different
              (Carrier.encodeString requestedFile)
              (includeBinding (Carrier.encodeString bindingFrom)
                (Carrier.encodeString bindingRequested)
                (Carrier.encodeString targetSource))
              (encodeBindingCount tailCount))
            (encodeBindingCount tailCount) := by
          apply eventuallyExact_of_one_step
          intro fuel
          exact bindingFromDecision_different_rewriteAt_exact fuel
            (Carrier.encodeString requestedFile)
            (includeBinding (Carrier.encodeString bindingFrom)
              (Carrier.encodeString bindingRequested)
              (Carrier.encodeString targetSource))
            (encodeBindingCount tailCount)
        have composed := eventuallyExact_of_two_premises
          (scanBindings (Carrier.encodeString fromSource)
            (Carrier.encodeString requestedFile)
            (Carrier.encodeIncludeBindings bindings))
          (encodeBindingCount tailCount)
          (bindingFromDecision PatternEqualityDecision.different
            (Carrier.encodeString requestedFile)
            (includeBinding (Carrier.encodeString bindingFrom)
              (Carrier.encodeString bindingRequested)
              (Carrier.encodeString targetSource))
            (encodeBindingCount tailCount))
          (encodeBindingCount tailCount)
          (scanBindings (Carrier.encodeString fromSource)
            (Carrier.encodeString requestedFile)
            (includeBindingsCons
              (includeBinding (Carrier.encodeString bindingFrom)
                (Carrier.encodeString bindingRequested)
                (Carrier.encodeString targetSource))
              (Carrier.encodeIncludeBindings bindings)))
          (encodeBindingCount tailCount)
          inductionHypothesis fromDecisionExact
          (fun fuel scanTail finishHead =>
            scanBindings_cons_different_rewriteAt_exact fuel
              (Carrier.encodeString fromSource)
              (Carrier.encodeString requestedFile)
              (Carrier.encodeString bindingFrom)
              (Carrier.encodeString bindingRequested)
              (Carrier.encodeString targetSource)
              (Carrier.encodeIncludeBindings bindings)
              (encodeBindingCount tailCount) (encodeBindingCount tailCount)
              differentFromEncoding scanTail finishHead)
        simpa [bindingMatches, tailCount, differentFrom,
          encodeIncludeBinding_eq] using composed

theorem lookupBinding_rewriteAt_exact (fuel : Nat)
    (fromSource requestedFile documents bindings count result : Pattern)
    (scanStep :
      rewriteAt base language fuel
          (scanBindings fromSource requestedFile bindings) = [count])
    (finishStep :
      rewriteAt base language fuel
          (finishBinding fromSource requestedFile count) = [result]) :
    rewriteAt base language (fuel + 1)
        (TptpOfficialIncludeEnvironmentLookupLanguageDef.lookupBinding
          fromSource requestedFile
          (sourceEnvironment documents bindings)) = [result] := by
  simp only [scanBindings, finishBinding, a] at scanStep finishStep
  change rewriteAt base language (fuel + 1)
    (.apply "tptp-include-lookup:lookup-binding"
      [fromSource, requestedFile,
       .apply "tptp-include-resolution:source-environment"
        [documents, bindings]]) = [result]
  rw [rewriteAt_eq_root_filter, bindingLookupRootRules]
  lookup_row_simp
  rw [scanStep]
  simp
  rw [finishStep]
  simp

theorem lookupBinding_encode_eventuallyExact
    (environment : SourceEnvironment) (fromSource requestedFile : String) :
    EventuallyExact
      (encodeBindingRequest environment fromSource requestedFile)
      (encodeBindingOutcome
        (TptpOfficialIncludeResolution.lookupBinding environment
          fromSource requestedFile)) := by
  let count := FiniteMatch.ofList
    (bindingMatches fromSource requestedFile environment.bindings)
  have scanExact := scanBindings_encode_eventuallyExact
    fromSource requestedFile environment.bindings
  have finishExact : EventuallyExact
      (finishBinding (Carrier.encodeString fromSource)
        (Carrier.encodeString requestedFile) (encodeBindingCount count))
      (encodeBindingOutcome
        (bindingOutcome fromSource requestedFile count)) := by
    apply eventuallyExact_of_one_step
    intro fuel
    exact finishBinding_rewriteAt_exact fuel fromSource requestedFile count
  have composed := eventuallyExact_of_two_premises
    (scanBindings (Carrier.encodeString fromSource)
      (Carrier.encodeString requestedFile)
      (Carrier.encodeIncludeBindings environment.bindings))
    (encodeBindingCount count)
    (finishBinding (Carrier.encodeString fromSource)
      (Carrier.encodeString requestedFile) (encodeBindingCount count))
    (encodeBindingOutcome
      (bindingOutcome fromSource requestedFile count))
    (encodeBindingRequest environment fromSource requestedFile)
    (encodeBindingOutcome
      (bindingOutcome fromSource requestedFile count))
    scanExact finishExact
    (fun fuel scanStep finishStep =>
      lookupBinding_rewriteAt_exact fuel
        (Carrier.encodeString fromSource)
        (Carrier.encodeString requestedFile)
        (Carrier.encodeSourceDocuments environment.documents)
        (Carrier.encodeIncludeBindings environment.bindings)
        (encodeBindingCount count)
        (encodeBindingOutcome
          (bindingOutcome fromSource requestedFile count))
        scanStep finishStep)
  rw [bindingOutcome_classification_eq_lookupBinding] at composed
  exact composed

namespace Canary

def emptyOfficialFile : Pattern :=
  .apply "tptp92-ast:tptp-file:alt-1"
    [.apply "tptp92-ast:tptp-input-list:alt-1" []]

def documentA : SourceDocument := {
  canonicalId := "A"
  digest := "digest-a"
  officialFile := emptyOfficialFile
}

def documentADuplicate : SourceDocument := {
  canonicalId := "A"
  digest := "digest-a-duplicate"
  officialFile := emptyOfficialFile
}

def bindingAX : IncludeBinding := {
  fromSource := "A"
  requestedFile := "x.p"
  targetSource := "AX"
}

def bindingBX : IncludeBinding := {
  fromSource := "B"
  requestedFile := "x.p"
  targetSource := "BX"
}

def bindingAXDuplicate : IncludeBinding := {
  fromSource := "A"
  requestedFile := "x.p"
  targetSource := "AX-duplicate"
}

def parentRelativeEnvironment : SourceEnvironment := {
  documents := [documentA]
  bindings := [bindingAX, bindingBX]
}

theorem unique_document_is_original_occurrence :
    TptpOfficialIncludeResolution.lookupDocument
        parentRelativeEnvironment "A" = .ok documentA := by
  rfl

theorem missing_document_fails_closed :
    TptpOfficialIncludeResolution.lookupDocument
        parentRelativeEnvironment "missing" =
      .error (.missingDocument "missing") := by
  rfl

theorem duplicate_document_is_ambiguous :
    TptpOfficialIncludeResolution.lookupDocument
        { parentRelativeEnvironment with
          documents := [documentA, documentADuplicate] } "A" =
      .error (.ambiguousDocument "A") := by
  rfl

theorem same_spelling_is_parent_relative :
    TptpOfficialIncludeResolution.lookupBinding
        parentRelativeEnvironment "A" "x.p" = .ok bindingAX ∧
      TptpOfficialIncludeResolution.lookupBinding
        parentRelativeEnvironment "B" "x.p" = .ok bindingBX := by
  decide +kernel

theorem missing_binding_fails_closed :
    TptpOfficialIncludeResolution.lookupBinding
        parentRelativeEnvironment "A" "missing.p" =
      .error (.missingBinding "A" "missing.p") := by
  rfl

theorem duplicate_binding_is_ambiguous :
    TptpOfficialIncludeResolution.lookupBinding
        { parentRelativeEnvironment with
          bindings := [bindingAX, bindingAXDuplicate] } "A" "x.p" =
      .error (.ambiguousBinding "A" "x.p") := by
  rfl

theorem declared_document_lookup_agrees :
    EventuallyExact
      (encodeDocumentRequest parentRelativeEnvironment "A")
      (encodeDocumentOutcome (.ok documentA)) := by
  simpa [unique_document_is_original_occurrence] using
    lookupDocument_encode_eventuallyExact parentRelativeEnvironment "A"

theorem declared_parent_relative_lookup_agrees :
    EventuallyExact
      (encodeBindingRequest parentRelativeEnvironment "B" "x.p")
      (encodeBindingOutcome (.ok bindingBX)) := by
  have exact := lookupBinding_encode_eventuallyExact
    parentRelativeEnvironment "B" "x.p"
  rw [same_spelling_is_parent_relative.2] at exact
  exact exact

end Canary

#print axioms documentOutcome_classification_eq_lookupDocument
#print axioms bindingOutcome_classification_eq_lookupBinding
#print axioms scanDocuments_encode_eventuallyExact
#print axioms lookupDocument_encode_eventuallyExact
#print axioms scanBindings_encode_eventuallyExact
#print axioms lookupBinding_encode_eventuallyExact
#print axioms Canary.unique_document_is_original_occurrence
#print axioms Canary.missing_document_fails_closed
#print axioms Canary.duplicate_document_is_ambiguous
#print axioms Canary.same_spelling_is_parent_relative
#print axioms Canary.missing_binding_fails_closed
#print axioms Canary.duplicate_binding_is_ambiguous
#print axioms Canary.declared_document_lookup_agrees
#print axioms Canary.declared_parent_relative_lookup_agrees

end Mettapedia.GSLT.LanguageDef.TptpOfficialIncludeEnvironmentLookupAgreement
