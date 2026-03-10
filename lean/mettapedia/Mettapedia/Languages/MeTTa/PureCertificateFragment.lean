import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
import Mettapedia.Languages.MeTTa.PureKernel.Context
import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Languages.MeTTa.PureKernel.Typing

/-!
# Restricted Pure Certificate Fragment

The first restricted proof-side certificate lane that `MeTTa-Pure` can
realistically check today.

This file isolates the current pure certificate story from the larger
`ElaboratedCore` classifier:

- a binder-aware closed surface syntax
- lowering to trusted `PureTm`
- lowering to the shared quoted MeTTa artifact
- a certificate stating those two views agree

This is intentionally small and closed. It is not a general theorem-proving
surface yet.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Small binder-aware surface syntax for the first real pure fragment above
`PureKernel`.

This mirrors the trusted Pure syntax closely on purpose: the immediate goal is
to make the first dual-view certificate real, not to invent a second kernel. -/
inductive SurfacePureTm : Nat → Type where
  | var : Fin n → SurfacePureTm n
  | u0 : SurfacePureTm n
  | u1 : SurfacePureTm n
  | pi : SurfacePureTm n → SurfacePureTm (n + 1) → SurfacePureTm n
  | sigma : SurfacePureTm n → SurfacePureTm (n + 1) → SurfacePureTm n
  | id : SurfacePureTm n → SurfacePureTm n → SurfacePureTm n → SurfacePureTm n
  | lam : SurfacePureTm (n + 1) → SurfacePureTm n
  | app : SurfacePureTm n → SurfacePureTm n → SurfacePureTm n
  | pair : SurfacePureTm n → SurfacePureTm n → SurfacePureTm n
  | fst : SurfacePureTm n → SurfacePureTm n
  | snd : SurfacePureTm n → SurfacePureTm n
  | refl : SurfacePureTm n → SurfacePureTm n
deriving DecidableEq, Repr

namespace SurfacePureTm

def toPureTm : SurfacePureTm n → PureTm n
  | .var i => .var i
  | .u0 => .u0
  | .u1 => .u1
  | .pi A B => .pi (toPureTm A) (toPureTm B)
  | .sigma A B => .sigma (toPureTm A) (toPureTm B)
  | .id A a b => .id (toPureTm A) (toPureTm a) (toPureTm b)
  | .lam b => .lam (toPureTm b)
  | .app f a => .app (toPureTm f) (toPureTm a)
  | .pair a b => .pair (toPureTm a) (toPureTm b)
  | .fst p => .fst (toPureTm p)
  | .snd p => .snd (toPureTm p)
  | .refl a => .refl (toPureTm a)

def toPatternWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : SurfacePureTm n → Pattern
  | .var i => .fvar (ρ i)
  | .u0 => Mettapedia.Languages.MeTTa.Pure.Core.u0
  | .u1 => Mettapedia.Languages.MeTTa.Pure.Core.u1
  | .pi A B =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Pure.Core.mkPi (toPatternWith ν k ρ A)
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) B))
  | .sigma A B =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Pure.Core.mkSigma (toPatternWith ν k ρ A)
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) B))
  | .id A a b =>
      Mettapedia.Languages.MeTTa.Pure.Core.mkId
        (toPatternWith ν k ρ A) (toPatternWith ν k ρ a) (toPatternWith ν k ρ b)
  | .lam b =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Pure.Core.mkLam
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) b))
  | .app f a =>
      Mettapedia.Languages.MeTTa.Pure.Core.mkApp (toPatternWith ν k ρ f) (toPatternWith ν k ρ a)
  | .pair a b =>
      Mettapedia.Languages.MeTTa.Pure.Core.mkPair (toPatternWith ν k ρ a) (toPatternWith ν k ρ b)
  | .fst p => Mettapedia.Languages.MeTTa.Pure.Core.mkFst (toPatternWith ν k ρ p)
  | .snd p => Mettapedia.Languages.MeTTa.Pure.Core.mkSnd (toPatternWith ν k ρ p)
  | .refl a => Mettapedia.Languages.MeTTa.Pure.Core.mkRefl (toPatternWith ν k ρ a)

def toPattern (ρ : QuoteEnv n) (t : SurfacePureTm n) : Pattern :=
  toPatternWith defaultBinderName 0 ρ t

def toClosedPattern (t : SurfacePureTm 0) : Pattern :=
  toPattern emptyEnv t

theorem toPatternWith_eq_quoteTmWith
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    ∀ t : SurfacePureTm n, toPatternWith ν k ρ t = quoteTmWith ν k ρ (toPureTm t)
  | .var i => rfl
  | .u0 => rfl
  | .u1 => rfl
  | .pi A B => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .sigma A B => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .id A a b => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .lam b => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .app f a => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .pair a b => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .fst p => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .snd p => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .refl a => by
      simp [toPatternWith, toPureTm, quoteTmWith, toPatternWith_eq_quoteTmWith]

theorem toPattern_eq_quoteTm (ρ : QuoteEnv n) (t : SurfacePureTm n) :
    toPattern ρ t = quoteTm ρ (toPureTm t) := by
  simpa [toPattern, quoteTm] using toPatternWith_eq_quoteTmWith defaultBinderName 0 ρ t

theorem toClosedPattern_eq_quoteClosedTm (t : SurfacePureTm 0) :
    toClosedPattern t = quoteClosedTm (toPureTm t) := by
  simpa [toClosedPattern, quoteClosedTm] using toPattern_eq_quoteTm emptyEnv t

end SurfacePureTm

/-- Certificate for the trusted Pure branch. -/
structure PureCertificate where
  term : PureTm 0
  artifact : SharedArtifact
  artifact_eq : artifact.pattern = quoteClosedTm term
  abcSurface : PureClosedABCSurface := defaultPureClosedABCSurface

/-- First real overlap certificate for a shared pure surface fragment.

This is the first nontrivial "both views at once" object:
- one binder-aware surface term,
- one trusted PureKernel term,
- one shared MeTTa artifact,
- and a proof that the two downstream views agree. -/
structure SharedPureOverlapCertificate where
  surface : SurfacePureTm 0
  pure : PureCertificate
  overlapClass : OverlapClass
  pure_eq : pure.term = surface.toPureTm
  artifact_eq_surface : pure.artifact.pattern = surface.toClosedPattern
  artifact_eq_pure : pure.artifact.pattern = quoteClosedTm pure.term

def SharedPureOverlapCertificate.backendName (_ : SharedPureOverlapCertificate) : String :=
  "PureKernel+Artifact"

def certifySurfacePure (surface : SurfacePureTm 0) : SharedPureOverlapCertificate :=
  let pure : PureCertificate := {
    term := surface.toPureTm
    artifact := ⟨surface.toClosedPattern⟩
    artifact_eq := by simpa using surface.toClosedPattern_eq_quoteClosedTm
  }
  {
    surface := surface
    pure := pure
    overlapClass := OverlapClass.artifactOnly
    pure_eq := rfl
    artifact_eq_surface := rfl
    artifact_eq_pure := pure.artifact_eq
  }

theorem certifySurfacePure_backendName (term : SurfacePureTm 0) :
    (certifySurfacePure term).backendName = "PureKernel+Artifact" := rfl

theorem certifySurfacePure_overlapClass (term : SurfacePureTm 0) :
    (certifySurfacePure term).overlapClass = OverlapClass.artifactOnly := rfl

theorem certifySurfacePure_overlapName (term : SurfacePureTm 0) :
    OverlapClass.name (certifySurfacePure term).overlapClass = "artifact-only" := rfl

theorem surfacePureClosed_overlap_is_not_directExec
    (term : SurfacePureTm 0) :
    (certifySurfacePure term).overlapClass ≠ OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifySurfacePure]

/-- First restricted import envelope for the current Pure certificate lane.

This is intentionally narrow: it carries only the currently honest certificate
objects that `MeTTa-Pure` can already justify, rather than pretending to import
arbitrary Lean proofs or arbitrary runtime claims.
-/
inductive PureCertificateImport where
  | pure (cert : PureCertificate)
  | overlap (cert : SharedPureOverlapCertificate)

def PureCertificateImport.artifact : PureCertificateImport → SharedArtifact
  | .pure cert => cert.artifact
  | .overlap cert => cert.pure.artifact

def PureCertificateImport.term : PureCertificateImport → PureTm 0
  | .pure cert => cert.term
  | .overlap cert => cert.pure.term

def PureCertificateImport.kindName : PureCertificateImport → String
  | .pure _ => "closed-pure"
  | .overlap _ => "shared-pure-overlap"

def PureCertificateImport.toPureCertificate : PureCertificateImport → PureCertificate
  | .pure cert => cert
  | .overlap cert => cert.pure

theorem PureCertificateImport.toPureCertificate_term
    (cert : PureCertificateImport) :
    cert.toPureCertificate.term = cert.term := by
  cases cert <;> rfl

theorem PureCertificateImport.toPureCertificate_artifact
    (cert : PureCertificateImport) :
    cert.toPureCertificate.artifact = cert.artifact := by
  cases cert <;> rfl

theorem PureCertificateImport.toPureCertificate_artifact_eq
    (cert : PureCertificateImport) :
    cert.toPureCertificate.artifact.pattern = quoteClosedTm cert.term := by
  cases cert with
  | pure cert =>
      simpa using cert.artifact_eq
  | overlap cert =>
      simpa [PureCertificateImport.term] using cert.artifact_eq_pure

/-- First real checked certificate object for the restricted Pure lane.

This is still intentionally small:
- closed Pure term only
- explicit claimed closed type
- explicit kernel typing witness in the empty context
- artifact view inherited from the imported Pure certificate
-/
structure CheckedPureCertificate where
  imported : PureCertificateImport
  claimedType : PureTm 0
  typing : HasType .nil imported.term claimedType

/-- Minimal judgment classes for the restricted Pure certificate lane.

This stays intentionally small: the current lane can honestly check closed
typing claims and quoted artifact agreement, but not broad theorem proving or
general proof import. -/
inductive PureJudgmentKind where
  | closedTyping
  | quotedArtifactAgreement
deriving DecidableEq, Repr

def PureJudgmentKind.name : PureJudgmentKind → String
  | .closedTyping => "closed-typing"
  | .quotedArtifactAgreement => "quoted-artifact-agreement"

def CheckedPureCertificate.term (cert : CheckedPureCertificate) : PureTm 0 :=
  cert.imported.term

def CheckedPureCertificate.artifact (cert : CheckedPureCertificate) : SharedArtifact :=
  cert.imported.artifact

def CheckedPureCertificate.kindName (cert : CheckedPureCertificate) : String :=
  cert.imported.kindName

def CheckedPureCertificate.region (_ : CheckedPureCertificate) : ElaboratedRegion :=
  ElaboratedRegion.pureKernelRegion

def CheckedPureCertificate.overlapClass (cert : CheckedPureCertificate) : OverlapClass :=
  match cert.imported with
  | .pure _ => OverlapClass.artifactOnly
  | .overlap cert => cert.overlapClass

def CheckedPureCertificate.backendName (_ : CheckedPureCertificate) : String :=
  "PureKernel+TypedCertificate"

/-- First explicit judgment layer above checked Pure certificates. -/
structure PureCertificateJudgment where
  kind : PureJudgmentKind
  certificate : CheckedPureCertificate

def PureCertificateJudgment.term (j : PureCertificateJudgment) : PureTm 0 :=
  j.certificate.term

def PureCertificateJudgment.claimedType (j : PureCertificateJudgment) : PureTm 0 :=
  j.certificate.claimedType

def PureCertificateJudgment.artifact (j : PureCertificateJudgment) : SharedArtifact :=
  j.certificate.artifact

def PureCertificateJudgment.region (j : PureCertificateJudgment) : ElaboratedRegion :=
  j.certificate.region

def PureCertificateJudgment.overlapClass (j : PureCertificateJudgment) : OverlapClass :=
  j.certificate.overlapClass

def PureCertificateJudgment.backendName (j : PureCertificateJudgment) : String :=
  j.certificate.backendName

theorem CheckedPureCertificate.term_eq_imported
    (cert : CheckedPureCertificate) :
    cert.term = cert.imported.term := rfl

theorem CheckedPureCertificate.artifact_eq_imported
    (cert : CheckedPureCertificate) :
    cert.artifact = cert.imported.artifact := rfl

theorem CheckedPureCertificate.quoteAgreement
    (cert : CheckedPureCertificate) :
    cert.artifact.pattern = quoteClosedTm cert.term := by
  simpa [CheckedPureCertificate.artifact, CheckedPureCertificate.term,
    PureCertificateImport.toPureCertificate_artifact,
    PureCertificateImport.toPureCertificate_term] using
    cert.imported.toPureCertificate_artifact_eq

theorem CheckedPureCertificate.emptyContextTyping
    (cert : CheckedPureCertificate) :
    HasType .nil cert.term cert.claimedType := by
  simpa [CheckedPureCertificate.term] using cert.typing

theorem CheckedPureCertificate.region_eq
    (cert : CheckedPureCertificate) :
    cert.region = ElaboratedRegion.pureKernelRegion := rfl

def CheckedPureCertificate.closedTypingJudgment
    (cert : CheckedPureCertificate) : PureCertificateJudgment :=
  { kind := .closedTyping
    certificate := cert }

def CheckedPureCertificate.quotedArtifactJudgment
    (cert : CheckedPureCertificate) : PureCertificateJudgment :=
  { kind := .quotedArtifactAgreement
    certificate := cert }

theorem CheckedPureCertificate.closedTypingJudgment_kind
    (cert : CheckedPureCertificate) :
    cert.closedTypingJudgment.kind = .closedTyping := rfl

theorem CheckedPureCertificate.quotedArtifactJudgment_kind
    (cert : CheckedPureCertificate) :
    cert.quotedArtifactJudgment.kind = .quotedArtifactAgreement := rfl

theorem PureCertificateJudgment.closedTyping_holds
    (cert : CheckedPureCertificate) :
    HasType .nil cert.closedTypingJudgment.term cert.closedTypingJudgment.claimedType := by
  simpa [CheckedPureCertificate.closedTypingJudgment, PureCertificateJudgment.term,
    PureCertificateJudgment.claimedType] using cert.emptyContextTyping

theorem PureCertificateJudgment.quotedArtifactAgreement_holds
    (cert : CheckedPureCertificate) :
    cert.quotedArtifactJudgment.artifact.pattern =
      quoteClosedTm cert.quotedArtifactJudgment.term := by
  simpa [CheckedPureCertificate.quotedArtifactJudgment, PureCertificateJudgment.artifact,
    PureCertificateJudgment.term] using cert.quoteAgreement

theorem PureCertificateJudgment.region_eq_pureKernel
    (j : PureCertificateJudgment) :
    j.region = ElaboratedRegion.pureKernelRegion := by
  simp [PureCertificateJudgment.region, CheckedPureCertificate.region_eq]

def checkImportedPureCertificate
    (imported : PureCertificateImport)
    (claimedType : PureTm 0)
    (typing : HasType .nil imported.term claimedType) :
    CheckedPureCertificate :=
  { imported := imported
    claimedType := claimedType
    typing := typing }

def CheckedPureCertificate.toPureCertificate (cert : CheckedPureCertificate) : PureCertificate :=
  cert.imported.toPureCertificate

def importPureCertificate (surface : SurfacePureTm 0) : PureCertificateImport :=
  .overlap (certifySurfacePure surface)

theorem importPureCertificate_kind (surface : SurfacePureTm 0) :
    (importPureCertificate surface).kindName = "shared-pure-overlap" := rfl

theorem importPureCertificate_term
    (surface : SurfacePureTm 0) :
    (importPureCertificate surface).term = surface.toPureTm := rfl

theorem importPureCertificate_artifact
    (surface : SurfacePureTm 0) :
    (importPureCertificate surface).artifact.pattern = surface.toClosedPattern := rfl

def certifyTypedSurfacePure
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    CheckedPureCertificate :=
  checkImportedPureCertificate (importPureCertificate surface) claimedType <| by
    simpa [importPureCertificate_term] using typing

theorem certifyTypedSurfacePure_kind
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (certifyTypedSurfacePure surface claimedType typing).kindName =
      "shared-pure-overlap" := by
  simp [certifyTypedSurfacePure, checkImportedPureCertificate,
    CheckedPureCertificate.kindName, importPureCertificate,
    PureCertificateImport.kindName]

theorem certifyTypedSurfacePure_term
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (certifyTypedSurfacePure surface claimedType typing).term = surface.toPureTm := by
  change (importPureCertificate surface).term = surface.toPureTm
  exact importPureCertificate_term surface

theorem certifyTypedSurfacePure_artifact
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (certifyTypedSurfacePure surface claimedType typing).artifact.pattern =
      surface.toClosedPattern := by
  change (importPureCertificate surface).artifact.pattern = surface.toClosedPattern
  exact importPureCertificate_artifact surface

theorem certifyTypedSurfacePure_overlap_is_not_directExec
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (certifyTypedSurfacePure surface claimedType typing).overlapClass ≠
      OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifyTypedSurfacePure, checkImportedPureCertificate,
    CheckedPureCertificate.overlapClass, importPureCertificate, certifySurfacePure]

theorem certifyTypedSurfacePure_typing
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    HasType .nil
      (certifyTypedSurfacePure surface claimedType typing).term
      (certifyTypedSurfacePure surface claimedType typing).claimedType := by
  simpa [certifyTypedSurfacePure_term] using
    (certifyTypedSurfacePure surface claimedType typing).emptyContextTyping

theorem certifyTypedSurfacePure_closedTypingJudgment
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (certifyTypedSurfacePure surface claimedType typing).closedTypingJudgment.kind =
      .closedTyping := rfl

theorem certifyTypedSurfacePure_quotedArtifactJudgment
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (certifyTypedSurfacePure surface claimedType typing).quotedArtifactJudgment.kind =
      .quotedArtifactAgreement := rfl

theorem certifyTypedSurfacePure_quotedArtifactAgreement
    (surface : SurfacePureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil surface.toPureTm claimedType) :
    (certifyTypedSurfacePure surface claimedType typing).quotedArtifactJudgment.artifact.pattern =
      quoteClosedTm (certifyTypedSurfacePure surface claimedType typing).quotedArtifactJudgment.term := by
  exact PureCertificateJudgment.quotedArtifactAgreement_holds
    (certifyTypedSurfacePure surface claimedType typing)

end Mettapedia.Languages.MeTTa.ElaboratedCore
