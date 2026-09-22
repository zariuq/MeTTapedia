import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CertificateFragment
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Confluence
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics

/-!
# two-sort Checking Service

An explicit theoremic checking/conversion layer above the restricted two-sort
certificate fragment.

This does not introduce a second kernel or a new normalization engine. It
packages the existing TwoSortPiSigmaId conversion facts into a small service API for:

- common-reduct conversion witnesses
- checked certificate conversion along definitional equality
- explicit judgment preservation after conversion
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services

open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Confluence
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationEnv
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics

/-- A theoremic conversion witness between two closed two-sort types, packaged by
exhibiting a common reduct. -/
structure ConversionWitness (A B : ScopedTerm 0) where
  commonReduct : ScopedTerm 0
  leftReduces : RedStar A commonReduct
  rightReduces : RedStar B commonReduct

namespace ConversionWitness

theorem leftConv {A B : ScopedTerm 0} (w : ConversionWitness A B) :
    Conv A w.commonReduct :=
  redStar_implies_conv w.leftReduces

theorem rightConv {A B : ScopedTerm 0} (w : ConversionWitness A B) :
    Conv B w.commonReduct :=
  redStar_implies_conv w.rightReduces

theorem toConv {A B : ScopedTerm 0} (w : ConversionWitness A B) :
    Conv A B := by
  exact Relation.EqvGen.trans _ _ _ w.leftConv (Relation.EqvGen.symm _ _ w.rightConv)

noncomputable def ofConv {A B : ScopedTerm 0} (h : Conv A B) : ConversionWitness A B :=
  let u := Classical.choose (church_rosser_conv h)
  let hA := (Classical.choose_spec (church_rosser_conv h)).1
  let hB := (Classical.choose_spec (church_rosser_conv h)).2
  { commonReduct := u
    leftReduces := hA
    rightReduces := hB }

theorem ofConv_toConv {A B : ScopedTerm 0} (h : Conv A B) :
    Conv A B := by
  exact (ofConv h).toConv

end ConversionWitness

/-- Conversion of a checked two-sort certificate to a definitionally equal claimed
type. -/
structure CheckedTwoSortConversion where
  original : CheckedTwoSortCertificate
  targetType : ScopedTerm 0
  witness : ConversionWitness original.claimedType targetType

namespace CheckedTwoSortConversion

def convertedCertificate (conv : CheckedTwoSortConversion) : CheckedTwoSortCertificate :=
  { imported := conv.original.imported
    claimedType := conv.targetType
    typing := HasType.conv conv.original.typing conv.witness.toConv }

def term (conv : CheckedTwoSortConversion) : ScopedTerm 0 :=
  conv.convertedCertificate.term

def artifact (conv : CheckedTwoSortConversion) : SharedArtifact :=
  conv.convertedCertificate.artifact

def overlapClass (conv : CheckedTwoSortConversion) : OverlapClass :=
  conv.convertedCertificate.overlapClass

def region (conv : CheckedTwoSortConversion) : ElaboratedRegion :=
  conv.convertedCertificate.region

def backendName (conv : CheckedTwoSortConversion) : String :=
  conv.convertedCertificate.backendName

theorem term_eq_original (conv : CheckedTwoSortConversion) :
    conv.term = conv.original.term := rfl

theorem artifact_eq_original (conv : CheckedTwoSortConversion) :
    conv.artifact = conv.original.artifact := rfl

theorem overlapClass_eq_original (conv : CheckedTwoSortConversion) :
    conv.overlapClass = conv.original.overlapClass := rfl

theorem region_eq_original (conv : CheckedTwoSortConversion) :
    conv.region = conv.original.region := rfl

theorem backendName_eq_original (conv : CheckedTwoSortConversion) :
    conv.backendName = conv.original.backendName := rfl

theorem typing (conv : CheckedTwoSortConversion) :
    HasType .nil conv.term conv.targetType := by
  simpa [term, convertedCertificate] using conv.convertedCertificate.emptyContextTyping

theorem quoteAgreement (conv : CheckedTwoSortConversion) :
    conv.artifact.pattern = quoteClosedTm conv.term := by
  simpa [artifact, term, convertedCertificate] using conv.convertedCertificate.quoteAgreement

def closedTypingJudgment (conv : CheckedTwoSortConversion) : TwoSortCertificateJudgment :=
  conv.convertedCertificate.closedTypingJudgment

def quotedArtifactJudgment (conv : CheckedTwoSortConversion) : TwoSortCertificateJudgment :=
  conv.convertedCertificate.quotedArtifactJudgment

theorem closedTypingJudgment_holds (conv : CheckedTwoSortConversion) :
    HasType .nil conv.closedTypingJudgment.term conv.closedTypingJudgment.claimedType := by
  simpa [closedTypingJudgment] using
    TwoSortCertificateJudgment.closedTyping_holds conv.convertedCertificate

theorem quotedArtifactAgreement_holds (conv : CheckedTwoSortConversion) :
    conv.quotedArtifactJudgment.artifact.pattern =
      quoteClosedTm conv.quotedArtifactJudgment.term := by
  simpa [quotedArtifactJudgment] using
    TwoSortCertificateJudgment.quotedArtifactAgreement_holds conv.convertedCertificate

end CheckedTwoSortConversion

/-- Convert a checked two-sort certificate along a theoremic conversion witness. -/
noncomputable def convertCheckedTwoSortCertificate
    (cert : CheckedTwoSortCertificate)
    (targetType : ScopedTerm 0)
    (h : Conv cert.claimedType targetType) :
    CheckedTwoSortConversion :=
  { original := cert
    targetType := targetType
    witness := ConversionWitness.ofConv h }

/-- Direct checked import with a conversion step from the imported typing claim
to a new definitionally equal target type. -/
noncomputable def checkImportedTwoSortCertificateUpToConv
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    CheckedTwoSortConversion :=
  convertCheckedTwoSortCertificate
    (checkImportedTwoSortCertificate imported sourceType typing)
    targetType
    (by simpa [checkImportedTwoSortCertificate] using hconv)

theorem checkImportedTwoSortCertificateUpToConv_term
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv).term =
      imported.term := by
  rfl

theorem checkImportedTwoSortCertificateUpToConv_artifact
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv).artifact =
      imported.artifact := by
  rfl

theorem checkImportedTwoSortCertificateUpToConv_typing
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    HasType .nil
      (checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv).term
      targetType := by
  exact (checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv).typing

theorem checkImportedTwoSortCertificateUpToConv_quoteAgreement
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv).artifact.pattern =
      quoteClosedTm (checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv).term := by
  exact (checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv).quoteAgreement

/-! ## Packaged checking boundary -/

/-- The current proof-side checking boundary above the restricted two-sort
certificate lane.

This packages what the present theoremic API can honestly do:
- check imported closed two-sort certificates,
- convert them along definitional equality,
- preserve closed typing,
- preserve quoted artifact agreement.

It does not claim a new kernel or a full normalization engine. -/
structure TwoSortCheckingBoundary where
  supportedJudgments : List TwoSortJudgmentKind
  region : ElaboratedRegion
  overlapClass : OverlapClass
  supportsImportedCertificates : Bool
  supportsConversion : Bool

/-- Canonical checking boundary for the current restricted two-sort lane. -/
def twoSortCheckingBoundary : TwoSortCheckingBoundary :=
  { supportedJudgments := [.closedTyping, .quotedArtifactAgreement]
    region := .twoSortKernelRegion
    overlapClass := .artifactOnly
    supportsImportedCertificates := true
    supportsConversion := true }

theorem twoSortCheckingBoundary_region :
    twoSortCheckingBoundary.region = .twoSortKernelRegion := rfl

theorem twoSortCheckingBoundary_overlap :
    twoSortCheckingBoundary.overlapClass = .artifactOnly := rfl

theorem twoSortCheckingBoundary_supports_closedTyping :
    TwoSortJudgmentKind.closedTyping ∈ twoSortCheckingBoundary.supportedJudgments := by
  simp [twoSortCheckingBoundary]

theorem twoSortCheckingBoundary_supports_quotedArtifactAgreement :
    TwoSortJudgmentKind.quotedArtifactAgreement ∈ twoSortCheckingBoundary.supportedJudgments := by
  simp [twoSortCheckingBoundary]

theorem twoSortCheckingBoundary_supports_import :
    twoSortCheckingBoundary.supportsImportedCertificates = true := rfl

theorem twoSortCheckingBoundary_supports_conversion :
    twoSortCheckingBoundary.supportsConversion = true := rfl

def closedTwoSortImport (term : ScopedTerm 0) : TwoSortCertificateImport :=
  .twoSort
    { term := term
      artifact := ⟨quoteClosedTm term⟩
      artifact_eq := rfl }

/-- Packaged import/check operation exposed by the current proof-side checking
boundary. -/
def TwoSortCheckingBoundary.checkImported
    (_svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil imported.term claimedType) :
    CheckedTwoSortCertificate :=
  checkImportedTwoSortCertificate imported claimedType typing

/-- Packaged check operation for a closed two-sort source term. -/
def TwoSortCheckingBoundary.checkSyntax
    (svc : TwoSortCheckingBoundary)
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    CheckedTwoSortCertificate :=
  svc.checkImported (importTwoSortCertificate sourceTerm) claimedType <| by
    simpa [importTwoSortCertificate_term] using typing

/-- Packaged check operation for an already-closed two-sort kernel term. -/
def TwoSortCheckingBoundary.checkClosedTerm
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil term claimedType) :
    CheckedTwoSortCertificate :=
  svc.checkImported (closedTwoSortImport term) claimedType typing

/-- Packaged import/check-and-convert operation exposed by the current proof-side
checking boundary. -/
noncomputable def TwoSortCheckingBoundary.checkImportedUpToConv
    (_svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    CheckedTwoSortConversion :=
  checkImportedTwoSortCertificateUpToConv imported sourceType targetType typing hconv

theorem TwoSortCheckingBoundary.checkImported_term
    (svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil imported.term claimedType) :
    (svc.checkImported imported claimedType typing).term = imported.term := by
  rfl

theorem TwoSortCheckingBoundary.checkImported_quoteAgreement
    (svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil imported.term claimedType) :
    (svc.checkImported imported claimedType typing).artifact.pattern =
      quoteClosedTm (svc.checkImported imported claimedType typing).term := by
  exact (svc.checkImported imported claimedType typing).quoteAgreement

theorem TwoSortCheckingBoundary.checkSyntax_term
    (svc : TwoSortCheckingBoundary)
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (svc.checkSyntax sourceTerm claimedType typing).term = sourceTerm.toScopedTerm := by
  rfl

theorem TwoSortCheckingBoundary.checkSyntax_quoteAgreement
    (svc : TwoSortCheckingBoundary)
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (svc.checkSyntax sourceTerm claimedType typing).artifact.pattern =
      quoteClosedTm (svc.checkSyntax sourceTerm claimedType typing).term := by
  exact (svc.checkSyntax sourceTerm claimedType typing).quoteAgreement

theorem TwoSortCheckingBoundary.checkClosedTerm_term
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil term claimedType) :
    (svc.checkClosedTerm term claimedType typing).term = term := by
  rfl

theorem TwoSortCheckingBoundary.checkClosedTerm_quoteAgreement
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil term claimedType) :
    (svc.checkClosedTerm term claimedType typing).artifact.pattern =
      quoteClosedTm (svc.checkClosedTerm term claimedType typing).term := by
  exact (svc.checkClosedTerm term claimedType typing).quoteAgreement

theorem TwoSortCheckingBoundary.checkImportedUpToConv_region
    (svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (svc.checkImportedUpToConv imported sourceType targetType typing hconv).region =
      .twoSortKernelRegion := by
  rfl

theorem TwoSortCheckingBoundary.checkImportedUpToConv_overlap_preserved
    (svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (svc.checkImportedUpToConv imported sourceType targetType typing hconv).overlapClass =
      (svc.checkImported imported sourceType typing).overlapClass := by
  exact (svc.checkImportedUpToConv imported sourceType targetType typing hconv).overlapClass_eq_original

theorem TwoSortCheckingBoundary.checkImportedUpToConv_typing
    (svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    HasType .nil
      (svc.checkImportedUpToConv imported sourceType targetType typing hconv).term
      targetType := by
  exact (svc.checkImportedUpToConv imported sourceType targetType typing hconv).typing

theorem TwoSortCheckingBoundary.checkImportedUpToConv_quoteAgreement
    (svc : TwoSortCheckingBoundary)
    (imported : TwoSortCertificateImport)
    (sourceType targetType : ScopedTerm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (svc.checkImportedUpToConv imported sourceType targetType typing hconv).artifact.pattern =
      quoteClosedTm (svc.checkImportedUpToConv imported sourceType targetType typing hconv).term := by
  exact (svc.checkImportedUpToConv imported sourceType targetType typing hconv).quoteAgreement

theorem TwoSortCheckingBoundary.checkClosedTerm_typing
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil term claimedType) :
    HasType .nil
      (svc.checkClosedTerm term claimedType typing).term
      claimedType := by
  simpa [TwoSortCheckingBoundary.checkClosedTerm, TwoSortCheckingBoundary.checkImported,
    checkImportedTwoSortCertificate, CheckedTwoSortCertificate.term, closedTwoSortImport,
    TwoSortCertificateImport.term] using typing

/-! ## Declaration-aware closed constant checking -/

/-- Parser-free checked declaration unfolding result for one closed constant.
This stays in the declaration-aware proof lane (`HasTypeDecl`/`RedDecl`) and is
packaged through the same two-sort checking boundary object. -/
structure CheckedDeclaredConstantDelta where
  env : DeclEnv
  wellFormed : DeclEnvWellFormed env
  constName : DeclName
  declaredType : ScopedTerm 0
  unfoldedValue : ScopedTerm 0
  typeLookup : typeOf? env constName = some declaredType
  valueLookup : valueOf? env constName = some unfoldedValue
  sourceTyping :
    HasTypeDecl env .nil ((.const constName : ScopedTerm 0)) (liftClosed declaredType)
  deltaStep :
    RedDecl env ((.const constName : ScopedTerm 0)) (liftClosed unfoldedValue)
  targetTyping :
    HasTypeDecl env .nil (liftClosed unfoldedValue) (liftClosed declaredType)

def CheckedDeclaredConstantDelta.sourceTerm
    (result : CheckedDeclaredConstantDelta) : ScopedTerm 0 :=
  .const result.constName

def CheckedDeclaredConstantDelta.targetTerm
    (result : CheckedDeclaredConstantDelta) : ScopedTerm 0 :=
  liftClosed result.unfoldedValue

def CheckedDeclaredConstantDelta.sourceArtifact
    (result : CheckedDeclaredConstantDelta) : SharedArtifact :=
  ⟨quoteClosedTm result.sourceTerm⟩

def CheckedDeclaredConstantDelta.targetArtifact
    (result : CheckedDeclaredConstantDelta) : SharedArtifact :=
  ⟨quoteClosedTm result.targetTerm⟩

theorem CheckedDeclaredConstantDelta.sourceQuoteAgreement
    (result : CheckedDeclaredConstantDelta) :
    result.sourceArtifact.pattern = quoteClosedTm result.sourceTerm := rfl

theorem CheckedDeclaredConstantDelta.targetQuoteAgreement
    (result : CheckedDeclaredConstantDelta) :
    result.targetArtifact.pattern = quoteClosedTm result.targetTerm := rfl

def TwoSortCheckingBoundary.checkDeclaredConstantDelta
    (_svc : TwoSortCheckingBoundary)
    (E : DeclEnv)
    (hWf : DeclEnvWellFormed E)
    (c : DeclName)
    (A0 v0 : ScopedTerm 0)
    (hType : typeOf? E c = some A0)
    (hVal : valueOf? E c = some v0) :
    CheckedDeclaredConstantDelta :=
  { env := E
    wellFormed := hWf
    constName := c
    declaredType := A0
    unfoldedValue := v0
    typeLookup := hType
    valueLookup := hVal
    sourceTyping := .const hType
    deltaStep := .deltaConst hVal
    targetTyping := hWf.valuesWellTyped hType hVal }

theorem TwoSortCheckingBoundary.checkDeclaredConstantDelta_preserves_type
    (svc : TwoSortCheckingBoundary)
    (E : DeclEnv)
    (hWf : DeclEnvWellFormed E)
    (c : DeclName)
    (A0 v0 : ScopedTerm 0)
    (hType : typeOf? E c = some A0)
    (hVal : valueOf? E c = some v0) :
    HasTypeDecl E .nil
      (TwoSortCheckingBoundary.checkDeclaredConstantDelta svc E hWf c A0 v0 hType hVal).targetTerm
      (liftClosed A0) := by
  exact (TwoSortCheckingBoundary.checkDeclaredConstantDelta svc E hWf c A0 v0 hType hVal).targetTyping

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services
