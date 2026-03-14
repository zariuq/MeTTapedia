import Mettapedia.Languages.MeTTa.PureCertificateFragment
import Mettapedia.Languages.MeTTa.PureKernel.Confluence
import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

/-!
# Pure Checking Service

An explicit theoremic checking/conversion layer above the restricted Pure
certificate fragment.

This does not introduce a second kernel or a new normalization engine. It
packages the existing PureKernel conversion facts into a small service API for:

- common-reduct conversion witnesses
- checked certificate conversion along definitional equality
- explicit judgment preservation after conversion
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Confluence
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationEnv
open Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics

/-- A theoremic conversion witness between two closed Pure types, packaged by
exhibiting a common reduct. -/
structure ConversionWitness (A B : PureTm 0) where
  commonReduct : PureTm 0
  leftReduces : RedStar A commonReduct
  rightReduces : RedStar B commonReduct

namespace ConversionWitness

theorem leftConv {A B : PureTm 0} (w : ConversionWitness A B) :
    Conv A w.commonReduct :=
  redStar_implies_conv w.leftReduces

theorem rightConv {A B : PureTm 0} (w : ConversionWitness A B) :
    Conv B w.commonReduct :=
  redStar_implies_conv w.rightReduces

theorem toConv {A B : PureTm 0} (w : ConversionWitness A B) :
    Conv A B := by
  exact Relation.EqvGen.trans _ _ _ w.leftConv (Relation.EqvGen.symm _ _ w.rightConv)

noncomputable def ofConv {A B : PureTm 0} (h : Conv A B) : ConversionWitness A B :=
  let u := Classical.choose (church_rosser_conv h)
  let hA := (Classical.choose_spec (church_rosser_conv h)).1
  let hB := (Classical.choose_spec (church_rosser_conv h)).2
  { commonReduct := u
    leftReduces := hA
    rightReduces := hB }

theorem ofConv_toConv {A B : PureTm 0} (h : Conv A B) :
    Conv A B := by
  exact (ofConv h).toConv

end ConversionWitness

/-- Conversion of a checked Pure certificate to a definitionally equal claimed
type. -/
structure CheckedPureConversion where
  original : CheckedPureCertificate
  targetType : PureTm 0
  witness : ConversionWitness original.claimedType targetType

namespace CheckedPureConversion

def convertedCertificate (conv : CheckedPureConversion) : CheckedPureCertificate :=
  { imported := conv.original.imported
    claimedType := conv.targetType
    typing := HasType.conv conv.original.typing conv.witness.toConv }

def term (conv : CheckedPureConversion) : PureTm 0 :=
  conv.convertedCertificate.term

def artifact (conv : CheckedPureConversion) : SharedArtifact :=
  conv.convertedCertificate.artifact

def overlapClass (conv : CheckedPureConversion) : OverlapClass :=
  conv.convertedCertificate.overlapClass

def region (conv : CheckedPureConversion) : ElaboratedRegion :=
  conv.convertedCertificate.region

def backendName (conv : CheckedPureConversion) : String :=
  conv.convertedCertificate.backendName

theorem term_eq_original (conv : CheckedPureConversion) :
    conv.term = conv.original.term := rfl

theorem artifact_eq_original (conv : CheckedPureConversion) :
    conv.artifact = conv.original.artifact := rfl

theorem overlapClass_eq_original (conv : CheckedPureConversion) :
    conv.overlapClass = conv.original.overlapClass := rfl

theorem region_eq_original (conv : CheckedPureConversion) :
    conv.region = conv.original.region := rfl

theorem backendName_eq_original (conv : CheckedPureConversion) :
    conv.backendName = conv.original.backendName := rfl

theorem typing (conv : CheckedPureConversion) :
    HasType .nil conv.term conv.targetType := by
  simpa [term, convertedCertificate] using conv.convertedCertificate.emptyContextTyping

theorem quoteAgreement (conv : CheckedPureConversion) :
    conv.artifact.pattern = quoteClosedTm conv.term := by
  simpa [artifact, term, convertedCertificate] using conv.convertedCertificate.quoteAgreement

def closedTypingJudgment (conv : CheckedPureConversion) : PureCertificateJudgment :=
  conv.convertedCertificate.closedTypingJudgment

def quotedArtifactJudgment (conv : CheckedPureConversion) : PureCertificateJudgment :=
  conv.convertedCertificate.quotedArtifactJudgment

theorem closedTypingJudgment_holds (conv : CheckedPureConversion) :
    HasType .nil conv.closedTypingJudgment.term conv.closedTypingJudgment.claimedType := by
  simpa [closedTypingJudgment] using
    PureCertificateJudgment.closedTyping_holds conv.convertedCertificate

theorem quotedArtifactAgreement_holds (conv : CheckedPureConversion) :
    conv.quotedArtifactJudgment.artifact.pattern =
      quoteClosedTm conv.quotedArtifactJudgment.term := by
  simpa [quotedArtifactJudgment] using
    PureCertificateJudgment.quotedArtifactAgreement_holds conv.convertedCertificate

end CheckedPureConversion

/-- Convert a checked Pure certificate along a theoremic conversion witness. -/
noncomputable def convertCheckedPureCertificate
    (cert : CheckedPureCertificate)
    (targetType : PureTm 0)
    (h : Conv cert.claimedType targetType) :
    CheckedPureConversion :=
  { original := cert
    targetType := targetType
    witness := ConversionWitness.ofConv h }

/-- Direct checked import with a conversion step from the imported typing claim
to a new definitionally equal target type. -/
noncomputable def checkImportedPureCertificateUpToConv
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    CheckedPureConversion :=
  convertCheckedPureCertificate
    (checkImportedPureCertificate imported sourceType typing)
    targetType
    (by simpa using hconv)

theorem checkImportedPureCertificateUpToConv_term
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv).term =
      imported.term := by
  rfl

theorem checkImportedPureCertificateUpToConv_artifact
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv).artifact =
      imported.artifact := by
  rfl

theorem checkImportedPureCertificateUpToConv_typing
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    HasType .nil
      (checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv).term
      targetType := by
  exact (checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv).typing

theorem checkImportedPureCertificateUpToConv_quoteAgreement
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv).artifact.pattern =
      quoteClosedTm (checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv).term := by
  exact (checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv).quoteAgreement

/-! ## Packaged checking boundary -/

/-- The current proof-side checking boundary above the restricted Pure
certificate lane.

This packages what the present theoremic API can honestly do:
- check imported closed Pure certificates,
- convert them along definitional equality,
- preserve closed typing,
- preserve quoted artifact agreement.

It does not claim a new kernel or a full normalization engine. -/
structure PureCheckingBoundary where
  supportedJudgments : List PureJudgmentKind
  region : ElaboratedRegion
  overlapClass : OverlapClass
  supportsImportedCertificates : Bool
  supportsConversion : Bool

/-- Canonical checking boundary for the current restricted Pure lane. -/
def pureCheckingBoundary : PureCheckingBoundary :=
  { supportedJudgments := [.closedTyping, .quotedArtifactAgreement]
    region := .pureKernelRegion
    overlapClass := .artifactOnly
    supportsImportedCertificates := true
    supportsConversion := true }

theorem pureCheckingBoundary_region :
    pureCheckingBoundary.region = .pureKernelRegion := rfl

theorem pureCheckingBoundary_overlap :
    pureCheckingBoundary.overlapClass = .artifactOnly := rfl

theorem pureCheckingBoundary_supports_closedTyping :
    PureJudgmentKind.closedTyping ∈ pureCheckingBoundary.supportedJudgments := by
  simp [pureCheckingBoundary]

theorem pureCheckingBoundary_supports_quotedArtifactAgreement :
    PureJudgmentKind.quotedArtifactAgreement ∈ pureCheckingBoundary.supportedJudgments := by
  simp [pureCheckingBoundary]

theorem pureCheckingBoundary_supports_import :
    pureCheckingBoundary.supportsImportedCertificates = true := rfl

theorem pureCheckingBoundary_supports_conversion :
    pureCheckingBoundary.supportsConversion = true := rfl

def closedPureImport (term : PureTm 0) : PureCertificateImport :=
  .pure
    { term := term
      artifact := ⟨quoteClosedTm term⟩
      artifact_eq := rfl }

/-- Packaged import/check operation exposed by the current proof-side checking
boundary. -/
def PureCheckingBoundary.checkImported
    (_svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (claimedType : PureTm 0)
    (typing : HasType .nil imported.term claimedType) :
    CheckedPureCertificate :=
  checkImportedPureCertificate imported claimedType typing

/-- Packaged check operation for a closed Pure surface term. -/
def PureCheckingBoundary.checkSurface
    (svc : PureCheckingBoundary)
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    CheckedPureCertificate :=
  svc.checkImported (importPureCertificate surface) claimedType <| by
    simpa [importPureCertificate_term] using typing

/-- Packaged check operation for an already-closed Pure kernel term. -/
def PureCheckingBoundary.checkClosedTerm
    (svc : PureCheckingBoundary)
    (term : PureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil term claimedType) :
    CheckedPureCertificate :=
  svc.checkImported (closedPureImport term) claimedType typing

/-- Packaged import/check-and-convert operation exposed by the current proof-side
checking boundary. -/
noncomputable def PureCheckingBoundary.checkImportedUpToConv
    (_svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    CheckedPureConversion :=
  checkImportedPureCertificateUpToConv imported sourceType targetType typing hconv

theorem PureCheckingBoundary.checkImported_term
    (svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (claimedType : PureTm 0)
    (typing : HasType .nil imported.term claimedType) :
    (svc.checkImported imported claimedType typing).term = imported.term := by
  rfl

theorem PureCheckingBoundary.checkImported_quoteAgreement
    (svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (claimedType : PureTm 0)
    (typing : HasType .nil imported.term claimedType) :
    (svc.checkImported imported claimedType typing).artifact.pattern =
      quoteClosedTm (svc.checkImported imported claimedType typing).term := by
  exact (svc.checkImported imported claimedType typing).quoteAgreement

theorem PureCheckingBoundary.checkSurface_term
    (svc : PureCheckingBoundary)
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (svc.checkSurface surface claimedType typing).term = surface.toPureTm := by
  rfl

theorem PureCheckingBoundary.checkSurface_quoteAgreement
    (svc : PureCheckingBoundary)
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (svc.checkSurface surface claimedType typing).artifact.pattern =
      quoteClosedTm (svc.checkSurface surface claimedType typing).term := by
  exact (svc.checkSurface surface claimedType typing).quoteAgreement

theorem PureCheckingBoundary.checkClosedTerm_term
    (svc : PureCheckingBoundary)
    (term : PureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil term claimedType) :
    (svc.checkClosedTerm term claimedType typing).term = term := by
  rfl

theorem PureCheckingBoundary.checkClosedTerm_quoteAgreement
    (svc : PureCheckingBoundary)
    (term : PureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil term claimedType) :
    (svc.checkClosedTerm term claimedType typing).artifact.pattern =
      quoteClosedTm (svc.checkClosedTerm term claimedType typing).term := by
  exact (svc.checkClosedTerm term claimedType typing).quoteAgreement

theorem PureCheckingBoundary.checkImportedUpToConv_region
    (svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (svc.checkImportedUpToConv imported sourceType targetType typing hconv).region =
      .pureKernelRegion := by
  rfl

theorem PureCheckingBoundary.checkImportedUpToConv_overlap_preserved
    (svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (svc.checkImportedUpToConv imported sourceType targetType typing hconv).overlapClass =
      (svc.checkImported imported sourceType typing).overlapClass := by
  exact (svc.checkImportedUpToConv imported sourceType targetType typing hconv).overlapClass_eq_original

theorem PureCheckingBoundary.checkImportedUpToConv_typing
    (svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    HasType .nil
      (svc.checkImportedUpToConv imported sourceType targetType typing hconv).term
      targetType := by
  exact (svc.checkImportedUpToConv imported sourceType targetType typing hconv).typing

theorem PureCheckingBoundary.checkImportedUpToConv_quoteAgreement
    (svc : PureCheckingBoundary)
    (imported : PureCertificateImport)
    (sourceType targetType : PureTm 0)
    (typing : HasType .nil imported.term sourceType)
    (hconv : Conv sourceType targetType) :
    (svc.checkImportedUpToConv imported sourceType targetType typing hconv).artifact.pattern =
      quoteClosedTm (svc.checkImportedUpToConv imported sourceType targetType typing hconv).term := by
  exact (svc.checkImportedUpToConv imported sourceType targetType typing hconv).quoteAgreement

theorem PureCheckingBoundary.checkClosedTerm_typing
    (svc : PureCheckingBoundary)
    (term : PureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil term claimedType) :
    HasType .nil
      (svc.checkClosedTerm term claimedType typing).term
      claimedType := by
  simpa [PureCheckingBoundary.checkClosedTerm] using typing

/-! ## Declaration-aware closed constant checking -/

/-- Parser-free checked declaration unfolding result for one closed constant.
This stays in the declaration-aware proof lane (`HasTypeDecl`/`RedDecl`) and is
packaged through the same Pure checking boundary object. -/
structure CheckedDeclaredConstantDelta where
  env : DeclEnv
  wellFormed : DeclEnvWellFormed env
  constName : DeclName
  declaredType : PureTm 0
  unfoldedValue : PureTm 0
  typeLookup : typeOf? env constName = some declaredType
  valueLookup : valueOf? env constName = some unfoldedValue
  sourceTyping :
    HasTypeDecl env .nil ((.const constName : PureTm 0)) (liftClosed declaredType)
  deltaStep :
    RedDecl env ((.const constName : PureTm 0)) (liftClosed unfoldedValue)
  targetTyping :
    HasTypeDecl env .nil (liftClosed unfoldedValue) (liftClosed declaredType)

def CheckedDeclaredConstantDelta.sourceTerm
    (result : CheckedDeclaredConstantDelta) : PureTm 0 :=
  .const result.constName

def CheckedDeclaredConstantDelta.targetTerm
    (result : CheckedDeclaredConstantDelta) : PureTm 0 :=
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

def PureCheckingBoundary.checkDeclaredConstantDelta
    (_svc : PureCheckingBoundary)
    (E : DeclEnv)
    (hWf : DeclEnvWellFormed E)
    (c : DeclName)
    (A0 v0 : PureTm 0)
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

theorem PureCheckingBoundary.checkDeclaredConstantDelta_preserves_type
    (svc : PureCheckingBoundary)
    (E : DeclEnv)
    (hWf : DeclEnvWellFormed E)
    (c : DeclName)
    (A0 v0 : PureTm 0)
    (hType : typeOf? E c = some A0)
    (hVal : valueOf? E c = some v0) :
    HasTypeDecl E .nil
      (PureCheckingBoundary.checkDeclaredConstantDelta svc E hWf c A0 v0 hType hVal).targetTerm
      (liftClosed A0) := by
  exact (PureCheckingBoundary.checkDeclaredConstantDelta svc E hWf c A0 v0 hType hVal).targetTyping

end Mettapedia.Languages.MeTTa.ElaboratedCore
