import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.CoreEmbedding
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing

/-!
# Restricted Pure Certificate Fragment

The first restricted proof-side certificate lane that `MeTTa-Pure` can
realistically check today.

This file isolates the current pure certificate story from the larger
`ElaboratedCore` classifier:

- a binder-aware closed concrete syntax
- lowering to trusted `PureTm`
- lowering to the shared quoted MeTTa artifact
- a certificate stating those two views agree

This is intentionally small and closed. It is not a general theorem-proving
syntax yet.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.CoreEmbedding
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Small binder-aware concrete syntax for the first real pure fragment above
`IntrinsicPure`.

This mirrors the trusted Pure syntax closely on purpose: the immediate goal is
to make the first dual-view certificate real, not to invent a second kernel. -/
inductive PureSyntaxTerm : Nat → Type where
  | var : Fin n → PureSyntaxTerm n
  | u0 : PureSyntaxTerm n
  | u1 : PureSyntaxTerm n
  | pi : PureSyntaxTerm n → PureSyntaxTerm (n + 1) → PureSyntaxTerm n
  | sigma : PureSyntaxTerm n → PureSyntaxTerm (n + 1) → PureSyntaxTerm n
  | id : PureSyntaxTerm n → PureSyntaxTerm n → PureSyntaxTerm n → PureSyntaxTerm n
  | lam : PureSyntaxTerm (n + 1) → PureSyntaxTerm n
  | app : PureSyntaxTerm n → PureSyntaxTerm n → PureSyntaxTerm n
  | pair : PureSyntaxTerm n → PureSyntaxTerm n → PureSyntaxTerm n
  | fst : PureSyntaxTerm n → PureSyntaxTerm n
  | snd : PureSyntaxTerm n → PureSyntaxTerm n
  | refl : PureSyntaxTerm n → PureSyntaxTerm n
deriving DecidableEq, Repr

namespace PureSyntaxTerm

def toPureTm : PureSyntaxTerm n → PureTm n
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

def toPatternWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : PureSyntaxTerm n → Pattern
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

def toPattern (ρ : QuoteEnv n) (t : PureSyntaxTerm n) : Pattern :=
  toPatternWith defaultBinderName 0 ρ t

def toClosedPattern (t : PureSyntaxTerm 0) : Pattern :=
  toPattern emptyEnv t

theorem toPatternWith_eq_quoteTmWith
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    ∀ t : PureSyntaxTerm n, toPatternWith ν k ρ t = quoteTmWith ν k ρ (toPureTm t)
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

theorem toPattern_eq_quoteTm (ρ : QuoteEnv n) (t : PureSyntaxTerm n) :
    toPattern ρ t = quoteTm ρ (toPureTm t) := by
  simpa [toPattern, quoteTm] using toPatternWith_eq_quoteTmWith defaultBinderName 0 ρ t

theorem toClosedPattern_eq_quoteClosedTm (t : PureSyntaxTerm 0) :
    toClosedPattern t = quoteClosedTm (toPureTm t) := by
  simpa [toClosedPattern, quoteClosedTm] using toPattern_eq_quoteTm emptyEnv t

end PureSyntaxTerm

/-- Certificate for the trusted Pure branch. -/
structure PureCertificate where
  term : PureTm 0
  artifact : SharedArtifact
  artifact_eq : artifact.pattern = quoteClosedTm term

/-- First real overlap certificate for a shared pure source fragment.

This is the first nontrivial "both views at once" object:
- one binder-aware source term,
- one trusted IntrinsicPure term,
- one shared MeTTa artifact,
- and a proof that the two downstream views agree. -/
structure SharedPureOverlapCertificate where
  sourceTerm : PureSyntaxTerm 0
  pure : PureCertificate
  overlapClass : OverlapClass
  pure_eq : pure.term = sourceTerm.toPureTm
  artifact_eq_source : pure.artifact.pattern = sourceTerm.toClosedPattern
  artifact_eq_pure : pure.artifact.pattern = quoteClosedTm pure.term

def SharedPureOverlapCertificate.backendName (_ : SharedPureOverlapCertificate) : String :=
  "IntrinsicPure+Artifact"

def certifyPureSyntax (sourceTerm : PureSyntaxTerm 0) : SharedPureOverlapCertificate :=
  let pure : PureCertificate := {
    term := sourceTerm.toPureTm
    artifact := ⟨sourceTerm.toClosedPattern⟩
    artifact_eq := by simpa using sourceTerm.toClosedPattern_eq_quoteClosedTm
  }
  {
    sourceTerm := sourceTerm
    pure := pure
    overlapClass := OverlapClass.artifactOnly
    pure_eq := rfl
    artifact_eq_source := rfl
    artifact_eq_pure := pure.artifact_eq
  }

theorem certifyPureSyntax_backendName (term : PureSyntaxTerm 0) :
    (certifyPureSyntax term).backendName = "IntrinsicPure+Artifact" := rfl

theorem certifyPureSyntax_overlapClass (term : PureSyntaxTerm 0) :
    (certifyPureSyntax term).overlapClass = OverlapClass.artifactOnly := rfl

theorem certifyPureSyntax_overlapName (term : PureSyntaxTerm 0) :
    OverlapClass.name (certifyPureSyntax term).overlapClass = "artifact-only" := rfl

theorem pureClosedSyntax_overlap_is_not_directExec
    (term : PureSyntaxTerm 0) :
    (certifyPureSyntax term).overlapClass ≠ OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifyPureSyntax]

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
      simpa [PureCertificateImport.toPureCertificate, PureCertificateImport.term]
        using cert.artifact_eq
  | overlap cert =>
      simpa [PureCertificateImport.toPureCertificate, PureCertificateImport.term]
        using cert.artifact_eq_pure

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
  "IntrinsicPure+TypedCertificate"

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
  cases cert with
  | mk imported claimedType typing =>
      cases imported with
      | pure importedCert =>
          simpa [CheckedPureCertificate.artifact, CheckedPureCertificate.term,
            PureCertificateImport.artifact, PureCertificateImport.term]
            using importedCert.artifact_eq
      | overlap importedCert =>
          simpa [CheckedPureCertificate.artifact, CheckedPureCertificate.term,
            PureCertificateImport.artifact, PureCertificateImport.term]
            using importedCert.artifact_eq_pure

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

def importPureCertificate (sourceTerm : PureSyntaxTerm 0) : PureCertificateImport :=
  .overlap (certifyPureSyntax sourceTerm)

theorem importPureCertificate_kind (sourceTerm : PureSyntaxTerm 0) :
    (importPureCertificate sourceTerm).kindName = "shared-pure-overlap" := rfl

theorem importPureCertificate_term
    (sourceTerm : PureSyntaxTerm 0) :
    (importPureCertificate sourceTerm).term = sourceTerm.toPureTm := rfl

theorem importPureCertificate_artifact
    (sourceTerm : PureSyntaxTerm 0) :
    (importPureCertificate sourceTerm).artifact.pattern = sourceTerm.toClosedPattern := rfl

def certifyTypedPureSyntax
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    CheckedPureCertificate :=
  checkImportedPureCertificate (importPureCertificate sourceTerm) claimedType <| by
    simpa [importPureCertificate_term] using typing

theorem certifyTypedPureSyntax_kind
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    (certifyTypedPureSyntax sourceTerm claimedType typing).kindName =
      "shared-pure-overlap" := by
  simp [certifyTypedPureSyntax, checkImportedPureCertificate,
    CheckedPureCertificate.kindName, importPureCertificate,
    PureCertificateImport.kindName]

theorem certifyTypedPureSyntax_term
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    (certifyTypedPureSyntax sourceTerm claimedType typing).term = sourceTerm.toPureTm := by
  change (importPureCertificate sourceTerm).term = sourceTerm.toPureTm
  exact importPureCertificate_term sourceTerm

theorem certifyTypedPureSyntax_artifact
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    (certifyTypedPureSyntax sourceTerm claimedType typing).artifact.pattern =
      sourceTerm.toClosedPattern := by
  change (importPureCertificate sourceTerm).artifact.pattern = sourceTerm.toClosedPattern
  exact importPureCertificate_artifact sourceTerm

theorem certifyTypedPureSyntax_overlap_is_not_directExec
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    (certifyTypedPureSyntax sourceTerm claimedType typing).overlapClass ≠
      OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifyTypedPureSyntax, checkImportedPureCertificate,
    CheckedPureCertificate.overlapClass, importPureCertificate, certifyPureSyntax]

theorem certifyTypedPureSyntax_typing
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    HasType .nil
      (certifyTypedPureSyntax sourceTerm claimedType typing).term
      (certifyTypedPureSyntax sourceTerm claimedType typing).claimedType := by
  simpa [certifyTypedPureSyntax_term] using
    (certifyTypedPureSyntax sourceTerm claimedType typing).emptyContextTyping

theorem certifyTypedPureSyntax_closedTypingJudgment
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    (certifyTypedPureSyntax sourceTerm claimedType typing).closedTypingJudgment.kind =
      .closedTyping := rfl

theorem certifyTypedPureSyntax_quotedArtifactJudgment
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    (certifyTypedPureSyntax sourceTerm claimedType typing).quotedArtifactJudgment.kind =
      .quotedArtifactAgreement := rfl

theorem certifyTypedPureSyntax_quotedArtifactAgreement
    (sourceTerm : PureSyntaxTerm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil sourceTerm.toPureTm claimedType) :
    (certifyTypedPureSyntax sourceTerm claimedType typing).quotedArtifactJudgment.artifact.pattern =
      quoteClosedTm (certifyTypedPureSyntax sourceTerm claimedType typing).quotedArtifactJudgment.term := by
  exact PureCertificateJudgment.quotedArtifactAgreement_holds
    (certifyTypedPureSyntax sourceTerm claimedType typing)

end Mettapedia.Languages.MeTTa.ElaboratedCore
