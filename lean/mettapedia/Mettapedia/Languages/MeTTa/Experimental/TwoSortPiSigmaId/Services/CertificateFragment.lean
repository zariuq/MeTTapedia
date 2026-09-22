import Mettapedia.Languages.MeTTa.ElaboratedCoreBase
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing

/-!
# Restricted two-sort certificate fragment

This file isolates closed two-sort certificates from the larger `ElaboratedCore`
classifier:

- a binder-aware closed concrete syntax
- lowering to the fixed `ScopedTerm` grammar
- lowering to the shared quoted MeTTa artifact
- a certificate stating those two views agree

This is intentionally small and closed. It is not a general theorem-proving
syntax yet.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services

open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Binder-aware concrete syntax mirroring `TwoSortPiSigmaId`. The certificate
relates its scoped and quoted views; it does not select a Prime kernel. -/
inductive TwoSortSyntaxTerm : Nat → Type where
  | var : Fin n → TwoSortSyntaxTerm n
  | u0 : TwoSortSyntaxTerm n
  | u1 : TwoSortSyntaxTerm n
  | pi : TwoSortSyntaxTerm n → TwoSortSyntaxTerm (n + 1) → TwoSortSyntaxTerm n
  | sigma : TwoSortSyntaxTerm n → TwoSortSyntaxTerm (n + 1) → TwoSortSyntaxTerm n
  | id : TwoSortSyntaxTerm n → TwoSortSyntaxTerm n → TwoSortSyntaxTerm n → TwoSortSyntaxTerm n
  | lam : TwoSortSyntaxTerm (n + 1) → TwoSortSyntaxTerm n
  | app : TwoSortSyntaxTerm n → TwoSortSyntaxTerm n → TwoSortSyntaxTerm n
  | pair : TwoSortSyntaxTerm n → TwoSortSyntaxTerm n → TwoSortSyntaxTerm n
  | fst : TwoSortSyntaxTerm n → TwoSortSyntaxTerm n
  | snd : TwoSortSyntaxTerm n → TwoSortSyntaxTerm n
  | refl : TwoSortSyntaxTerm n → TwoSortSyntaxTerm n
deriving DecidableEq, Repr

namespace TwoSortSyntaxTerm

def toScopedTerm : TwoSortSyntaxTerm n → ScopedTerm n
  | .var i => .var i
  | .u0 => .u0
  | .u1 => .u1
  | .pi A B => .pi (toScopedTerm A) (toScopedTerm B)
  | .sigma A B => .sigma (toScopedTerm A) (toScopedTerm B)
  | .id A a b => .id (toScopedTerm A) (toScopedTerm a) (toScopedTerm b)
  | .lam b => .lam (toScopedTerm b)
  | .app f a => .app (toScopedTerm f) (toScopedTerm a)
  | .pair a b => .pair (toScopedTerm a) (toScopedTerm b)
  | .fst p => .fst (toScopedTerm p)
  | .snd p => .snd (toScopedTerm p)
  | .refl a => .refl (toScopedTerm a)

def toPatternWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : TwoSortSyntaxTerm n → Pattern
  | .var i => .fvar (ρ i)
  | .u0 => Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.u0
  | .u1 => Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.u1
  | .pi A B =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkPi (toPatternWith ν k ρ A)
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) B))
  | .sigma A B =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkSigma (toPatternWith ν k ρ A)
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) B))
  | .id A a b =>
      Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkId
        (toPatternWith ν k ρ A) (toPatternWith ν k ρ a) (toPatternWith ν k ρ b)
  | .lam b =>
      let x := ν k
      Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkLam
        (Mettapedia.OSLF.MeTTaIL.Substitution.closeFVar 0 x
          (toPatternWith ν (k + 1) (envCons x ρ) b))
  | .app f a =>
      Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkApp (toPatternWith ν k ρ f) (toPatternWith ν k ρ a)
  | .pair a b =>
      Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkPair (toPatternWith ν k ρ a) (toPatternWith ν k ρ b)
  | .fst p => Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkFst (toPatternWith ν k ρ p)
  | .snd p => Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkSnd (toPatternWith ν k ρ p)
  | .refl a => Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core.mkRefl (toPatternWith ν k ρ a)

def toPattern (ρ : QuoteEnv n) (t : TwoSortSyntaxTerm n) : Pattern :=
  toPatternWith defaultBinderName 0 ρ t

def toClosedPattern (t : TwoSortSyntaxTerm 0) : Pattern :=
  toPattern emptyEnv t

theorem toPatternWith_eq_quoteTmWith
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    ∀ t : TwoSortSyntaxTerm n, toPatternWith ν k ρ t = quoteTmWith ν k ρ (toScopedTerm t)
  | .var i => rfl
  | .u0 => rfl
  | .u1 => rfl
  | .pi A B => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .sigma A B => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .id A a b => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .lam b => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .app f a => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .pair a b => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .fst p => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .snd p => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]
  | .refl a => by
      simp [toPatternWith, toScopedTerm, quoteTmWith, toPatternWith_eq_quoteTmWith]

theorem toPattern_eq_quoteTm (ρ : QuoteEnv n) (t : TwoSortSyntaxTerm n) :
    toPattern ρ t = quoteTm ρ (toScopedTerm t) := by
  simpa [toPattern, quoteTm] using toPatternWith_eq_quoteTmWith defaultBinderName 0 ρ t

theorem toClosedPattern_eq_quoteClosedTm (t : TwoSortSyntaxTerm 0) :
    toClosedPattern t = quoteClosedTm (toScopedTerm t) := by
  simpa [toClosedPattern, quoteClosedTm] using toPattern_eq_quoteTm emptyEnv t

end TwoSortSyntaxTerm

/-- Certificate for the fixed two-sort branch. -/
structure TwoSortCertificate where
  term : ScopedTerm 0
  artifact : SharedArtifact
  artifact_eq : artifact.pattern = quoteClosedTm term

/-- First real overlap certificate for a shared twoSort source fragment.

This is the first nontrivial "both views at once" object:
- one binder-aware source term,
- one scoped TwoSortPiSigmaId term,
- one shared MeTTa artifact,
- and a proof that the two downstream views agree. -/
structure SharedTwoSortOverlapCertificate where
  sourceTerm : TwoSortSyntaxTerm 0
  twoSort : TwoSortCertificate
  overlapClass : OverlapClass
  twoSort_eq : twoSort.term = sourceTerm.toScopedTerm
  artifact_eq_source : twoSort.artifact.pattern = sourceTerm.toClosedPattern
  artifact_eq_twoSort : twoSort.artifact.pattern = quoteClosedTm twoSort.term

def SharedTwoSortOverlapCertificate.backendName (_ : SharedTwoSortOverlapCertificate) : String :=
  "TwoSortPiSigmaId+Artifact"

def certifyTwoSortSyntax (sourceTerm : TwoSortSyntaxTerm 0) : SharedTwoSortOverlapCertificate :=
  let twoSort : TwoSortCertificate := {
    term := sourceTerm.toScopedTerm
    artifact := ⟨sourceTerm.toClosedPattern⟩
    artifact_eq := by simpa using sourceTerm.toClosedPattern_eq_quoteClosedTm
  }
  {
    sourceTerm := sourceTerm
    twoSort := twoSort
    overlapClass := OverlapClass.artifactOnly
    twoSort_eq := rfl
    artifact_eq_source := rfl
    artifact_eq_twoSort := twoSort.artifact_eq
  }

theorem certifyTwoSortSyntax_backendName (term : TwoSortSyntaxTerm 0) :
    (certifyTwoSortSyntax term).backendName = "TwoSortPiSigmaId+Artifact" := rfl

theorem certifyTwoSortSyntax_overlapClass (term : TwoSortSyntaxTerm 0) :
    (certifyTwoSortSyntax term).overlapClass = OverlapClass.artifactOnly := rfl

theorem certifyTwoSortSyntax_overlapName (term : TwoSortSyntaxTerm 0) :
    OverlapClass.name (certifyTwoSortSyntax term).overlapClass = "artifact-only" := rfl

theorem twoSortClosedSyntax_overlap_is_not_directExec
    (term : TwoSortSyntaxTerm 0) :
    (certifyTwoSortSyntax term).overlapClass ≠ OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifyTwoSortSyntax]

/-- First restricted import envelope for the current two-sort certificate lane.

This is intentionally narrow: it carries only the currently honest certificate
objects that `the two-sort experiment` can already justify, rather than pretending to import
arbitrary Lean proofs or arbitrary runtime claims.
-/
inductive TwoSortCertificateImport where
  | twoSort (cert : TwoSortCertificate)
  | overlap (cert : SharedTwoSortOverlapCertificate)

def TwoSortCertificateImport.artifact : TwoSortCertificateImport → SharedArtifact
  | .twoSort cert => cert.artifact
  | .overlap cert => cert.twoSort.artifact

def TwoSortCertificateImport.term : TwoSortCertificateImport → ScopedTerm 0
  | .twoSort cert => cert.term
  | .overlap cert => cert.twoSort.term

def TwoSortCertificateImport.kindName : TwoSortCertificateImport → String
  | .twoSort _ => "closed-twoSort"
  | .overlap _ => "shared-twoSort-overlap"

def TwoSortCertificateImport.toTwoSortCertificate : TwoSortCertificateImport → TwoSortCertificate
  | .twoSort cert => cert
  | .overlap cert => cert.twoSort

theorem TwoSortCertificateImport.toTwoSortCertificate_term
    (cert : TwoSortCertificateImport) :
    cert.toTwoSortCertificate.term = cert.term := by
  cases cert <;> rfl

theorem TwoSortCertificateImport.toTwoSortCertificate_artifact
    (cert : TwoSortCertificateImport) :
    cert.toTwoSortCertificate.artifact = cert.artifact := by
  cases cert <;> rfl

theorem TwoSortCertificateImport.toTwoSortCertificate_artifact_eq
    (cert : TwoSortCertificateImport) :
    cert.toTwoSortCertificate.artifact.pattern = quoteClosedTm cert.term := by
  cases cert with
  | twoSort cert =>
      simpa [TwoSortCertificateImport.toTwoSortCertificate, TwoSortCertificateImport.term]
        using cert.artifact_eq
  | overlap cert =>
      simpa [TwoSortCertificateImport.toTwoSortCertificate, TwoSortCertificateImport.term]
        using cert.artifact_eq_twoSort

/-- First real checked certificate object for the restricted two-sort lane.

This is still intentionally small:
- closed two-sort term only
- explicit claimed closed type
- explicit kernel typing witness in the empty context
- artifact view inherited from the imported two-sort certificate
-/
structure CheckedTwoSortCertificate where
  imported : TwoSortCertificateImport
  claimedType : ScopedTerm 0
  typing : HasType .nil imported.term claimedType

/-- Minimal judgment classes for the restricted two-sort certificate lane.

This stays intentionally small: the current lane can honestly check closed
typing claims and quoted artifact agreement, but not broad theorem proving or
general proof import. -/
inductive TwoSortJudgmentKind where
  | closedTyping
  | quotedArtifactAgreement
deriving DecidableEq, Repr

def TwoSortJudgmentKind.name : TwoSortJudgmentKind → String
  | .closedTyping => "closed-typing"
  | .quotedArtifactAgreement => "quoted-artifact-agreement"

def CheckedTwoSortCertificate.term (cert : CheckedTwoSortCertificate) : ScopedTerm 0 :=
  cert.imported.term

def CheckedTwoSortCertificate.artifact (cert : CheckedTwoSortCertificate) : SharedArtifact :=
  cert.imported.artifact

def CheckedTwoSortCertificate.kindName (cert : CheckedTwoSortCertificate) : String :=
  cert.imported.kindName

def CheckedTwoSortCertificate.region (_ : CheckedTwoSortCertificate) : ElaboratedRegion :=
  ElaboratedRegion.twoSortKernelRegion

def CheckedTwoSortCertificate.overlapClass (cert : CheckedTwoSortCertificate) : OverlapClass :=
  match cert.imported with
  | .twoSort _ => OverlapClass.artifactOnly
  | .overlap cert => cert.overlapClass

def CheckedTwoSortCertificate.backendName (_ : CheckedTwoSortCertificate) : String :=
  "TwoSortPiSigmaId+TypedCertificate"

/-- First explicit judgment layer above checked two-sort certificates. -/
structure TwoSortCertificateJudgment where
  kind : TwoSortJudgmentKind
  certificate : CheckedTwoSortCertificate

def TwoSortCertificateJudgment.term (j : TwoSortCertificateJudgment) : ScopedTerm 0 :=
  j.certificate.term

def TwoSortCertificateJudgment.claimedType (j : TwoSortCertificateJudgment) : ScopedTerm 0 :=
  j.certificate.claimedType

def TwoSortCertificateJudgment.artifact (j : TwoSortCertificateJudgment) : SharedArtifact :=
  j.certificate.artifact

def TwoSortCertificateJudgment.region (j : TwoSortCertificateJudgment) : ElaboratedRegion :=
  j.certificate.region

def TwoSortCertificateJudgment.overlapClass (j : TwoSortCertificateJudgment) : OverlapClass :=
  j.certificate.overlapClass

def TwoSortCertificateJudgment.backendName (j : TwoSortCertificateJudgment) : String :=
  j.certificate.backendName

theorem CheckedTwoSortCertificate.term_eq_imported
    (cert : CheckedTwoSortCertificate) :
    cert.term = cert.imported.term := rfl

theorem CheckedTwoSortCertificate.artifact_eq_imported
    (cert : CheckedTwoSortCertificate) :
    cert.artifact = cert.imported.artifact := rfl

theorem CheckedTwoSortCertificate.quoteAgreement
    (cert : CheckedTwoSortCertificate) :
    cert.artifact.pattern = quoteClosedTm cert.term := by
  cases cert with
  | mk imported claimedType typing =>
      cases imported with
      | twoSort importedCert =>
          simpa [CheckedTwoSortCertificate.artifact, CheckedTwoSortCertificate.term,
            TwoSortCertificateImport.artifact, TwoSortCertificateImport.term]
            using importedCert.artifact_eq
      | overlap importedCert =>
          simpa [CheckedTwoSortCertificate.artifact, CheckedTwoSortCertificate.term,
            TwoSortCertificateImport.artifact, TwoSortCertificateImport.term]
            using importedCert.artifact_eq_twoSort

theorem CheckedTwoSortCertificate.emptyContextTyping
    (cert : CheckedTwoSortCertificate) :
    HasType .nil cert.term cert.claimedType := by
  simpa [CheckedTwoSortCertificate.term] using cert.typing

theorem CheckedTwoSortCertificate.region_eq
    (cert : CheckedTwoSortCertificate) :
    cert.region = ElaboratedRegion.twoSortKernelRegion := rfl

def CheckedTwoSortCertificate.closedTypingJudgment
    (cert : CheckedTwoSortCertificate) : TwoSortCertificateJudgment :=
  { kind := .closedTyping
    certificate := cert }

def CheckedTwoSortCertificate.quotedArtifactJudgment
    (cert : CheckedTwoSortCertificate) : TwoSortCertificateJudgment :=
  { kind := .quotedArtifactAgreement
    certificate := cert }

theorem CheckedTwoSortCertificate.closedTypingJudgment_kind
    (cert : CheckedTwoSortCertificate) :
    cert.closedTypingJudgment.kind = .closedTyping := rfl

theorem CheckedTwoSortCertificate.quotedArtifactJudgment_kind
    (cert : CheckedTwoSortCertificate) :
    cert.quotedArtifactJudgment.kind = .quotedArtifactAgreement := rfl

theorem TwoSortCertificateJudgment.closedTyping_holds
    (cert : CheckedTwoSortCertificate) :
    HasType .nil cert.closedTypingJudgment.term cert.closedTypingJudgment.claimedType := by
  simpa [CheckedTwoSortCertificate.closedTypingJudgment, TwoSortCertificateJudgment.term,
    TwoSortCertificateJudgment.claimedType] using cert.emptyContextTyping

theorem TwoSortCertificateJudgment.quotedArtifactAgreement_holds
    (cert : CheckedTwoSortCertificate) :
    cert.quotedArtifactJudgment.artifact.pattern =
      quoteClosedTm cert.quotedArtifactJudgment.term := by
  simpa [CheckedTwoSortCertificate.quotedArtifactJudgment, TwoSortCertificateJudgment.artifact,
    TwoSortCertificateJudgment.term] using cert.quoteAgreement

theorem TwoSortCertificateJudgment.region_eq_twoSortKernel
    (j : TwoSortCertificateJudgment) :
    j.region = ElaboratedRegion.twoSortKernelRegion := by
  simp [TwoSortCertificateJudgment.region, CheckedTwoSortCertificate.region_eq]

def checkImportedTwoSortCertificate
    (imported : TwoSortCertificateImport)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil imported.term claimedType) :
    CheckedTwoSortCertificate :=
  { imported := imported
    claimedType := claimedType
    typing := typing }

def CheckedTwoSortCertificate.toTwoSortCertificate (cert : CheckedTwoSortCertificate) : TwoSortCertificate :=
  cert.imported.toTwoSortCertificate

def importTwoSortCertificate (sourceTerm : TwoSortSyntaxTerm 0) : TwoSortCertificateImport :=
  .overlap (certifyTwoSortSyntax sourceTerm)

theorem importTwoSortCertificate_kind (sourceTerm : TwoSortSyntaxTerm 0) :
    (importTwoSortCertificate sourceTerm).kindName = "shared-twoSort-overlap" := rfl

theorem importTwoSortCertificate_term
    (sourceTerm : TwoSortSyntaxTerm 0) :
    (importTwoSortCertificate sourceTerm).term = sourceTerm.toScopedTerm := rfl

theorem importTwoSortCertificate_artifact
    (sourceTerm : TwoSortSyntaxTerm 0) :
    (importTwoSortCertificate sourceTerm).artifact.pattern = sourceTerm.toClosedPattern := rfl

def certifyTypedTwoSortSyntax
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    CheckedTwoSortCertificate :=
  checkImportedTwoSortCertificate (importTwoSortCertificate sourceTerm) claimedType <| by
    simpa [importTwoSortCertificate_term] using typing

theorem certifyTypedTwoSortSyntax_kind
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).kindName =
      "shared-twoSort-overlap" := by
  simp [certifyTypedTwoSortSyntax, checkImportedTwoSortCertificate,
    CheckedTwoSortCertificate.kindName, importTwoSortCertificate,
    TwoSortCertificateImport.kindName]

theorem certifyTypedTwoSortSyntax_term
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).term = sourceTerm.toScopedTerm := by
  change (importTwoSortCertificate sourceTerm).term = sourceTerm.toScopedTerm
  exact importTwoSortCertificate_term sourceTerm

theorem certifyTypedTwoSortSyntax_artifact
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).artifact.pattern =
      sourceTerm.toClosedPattern := by
  change (importTwoSortCertificate sourceTerm).artifact.pattern = sourceTerm.toClosedPattern
  exact importTwoSortCertificate_artifact sourceTerm

theorem certifyTypedTwoSortSyntax_overlap_is_not_directExec
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).overlapClass ≠
      OverlapClass.directExec morkRuntimeExec0 := by
  simp [certifyTypedTwoSortSyntax, checkImportedTwoSortCertificate,
    CheckedTwoSortCertificate.overlapClass, importTwoSortCertificate, certifyTwoSortSyntax]

theorem certifyTypedTwoSortSyntax_typing
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    HasType .nil
      (certifyTypedTwoSortSyntax sourceTerm claimedType typing).term
      (certifyTypedTwoSortSyntax sourceTerm claimedType typing).claimedType := by
  simpa [certifyTypedTwoSortSyntax_term] using
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).emptyContextTyping

theorem certifyTypedTwoSortSyntax_closedTypingJudgment
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).closedTypingJudgment.kind =
      .closedTyping := rfl

theorem certifyTypedTwoSortSyntax_quotedArtifactJudgment
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).quotedArtifactJudgment.kind =
      .quotedArtifactAgreement := rfl

theorem certifyTypedTwoSortSyntax_quotedArtifactAgreement
    (sourceTerm : TwoSortSyntaxTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil sourceTerm.toScopedTerm claimedType) :
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing).quotedArtifactJudgment.artifact.pattern =
      quoteClosedTm (certifyTypedTwoSortSyntax sourceTerm claimedType typing).quotedArtifactJudgment.term := by
  exact TwoSortCertificateJudgment.quotedArtifactAgreement_holds
    (certifyTypedTwoSortSyntax sourceTerm claimedType typing)

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services
