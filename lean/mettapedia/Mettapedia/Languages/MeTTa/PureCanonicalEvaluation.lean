import Mettapedia.Languages.MeTTa.PureNormalizationService
import Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
import Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

/-!
# Pure Canonical Evaluation Service

Parser-free checked canonicalization over the live trusted `PureKernel`.

This module intentionally stays inside the purified kernel boundary:

- closed `PureTm` inputs,
- closed typing proofs,
- canonicalization through `cdev`,
- output typing by subject reduction,
- quoted artifact and profile-theory consequences.

It does **not** reintroduce the archived prototype parser, fuel evaluator, or
CLI tooling.
-/

namespace Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Reduction
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel.SubjectReduction
open Mettapedia.Languages.MeTTa.PureKernel.CoreEmbedding
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.ProfileTheory

theorem subjectReductionRedStar {Γ : Ctx n} {t u A : PureTm n}
    (ht : HasType Γ t A) (h : RedStar t u) :
    HasType Γ u A := by
  induction h generalizing A with
  | refl =>
      simpa using ht
  | tail htu huv ih =>
      exact subject_reduction (ih ht) huv

/-- Checked canonicalization of a closed Pure term through the live canonical
development service. -/
structure CheckedCanonicalEvaluation where
  input : PureTm 0
  claimedType : PureTm 0
  inputTyping : HasType .nil input claimedType
  canonical : CanonicalClosedPureTerm
  canonicalInput_eq : canonical.input = input
  outputTyping : HasType .nil canonical.canonicalDevelopment claimedType

def CheckedCanonicalEvaluation.inputArtifact
    (result : CheckedCanonicalEvaluation) : SharedArtifact :=
  ⟨quoteClosedTm result.input⟩

def CheckedCanonicalEvaluation.canonicalArtifact
    (result : CheckedCanonicalEvaluation) : SharedArtifact :=
  result.canonical.artifact

theorem CheckedCanonicalEvaluation.inputQuoteAgreement
    (result : CheckedCanonicalEvaluation) :
    result.inputArtifact.pattern = quoteClosedTm result.input := rfl

theorem CheckedCanonicalEvaluation.canonicalQuoteAgreement
    (result : CheckedCanonicalEvaluation) :
    result.canonicalArtifact.pattern =
      quoteClosedTm result.canonical.canonicalDevelopment :=
  result.canonical.quoteAgreement

theorem CheckedCanonicalEvaluation.profileBridge
    (result : CheckedCanonicalEvaluation)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv) :
    PureProfileTheoryStepStar
      (quoteClosedTm result.input)
      (quoteClosedTm result.canonical.canonicalDevelopment) := by
  have hred : RedStar result.input result.canonical.canonicalDevelopment := by
    simpa [result.canonicalInput_eq] using
      result.canonical.reductionToCanonicalDevelopment
  exact pureTheoryStepStar_sound_pureProfileTheoryStepStar_quoteClosed hinst0 hcompat0 hred

def PureCheckingBoundary.checkAndCanonicalizeClosedTerm
    (svc : PureCheckingBoundary)
    (term : PureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil term claimedType) :
    CheckedCanonicalEvaluation :=
  let canonical := svc.canonicalizeClosed term
  let outputTyping :=
    subjectReductionRedStar typing canonical.reductionToCanonicalDevelopment
  { input := term
    claimedType := claimedType
    inputTyping := typing
    canonical := canonical
    canonicalInput_eq := svc.canonicalizeClosed_term term
    outputTyping := outputTyping }

theorem PureCheckingBoundary.checkAndCanonicalizeClosedTerm_preserves_type
    (svc : PureCheckingBoundary)
    (term : PureTm 0)
    (claimedType : PureTm 0)
    (typing : HasType .nil term claimedType) :
    (svc.checkAndCanonicalizeClosedTerm term claimedType typing).outputTyping =
      subjectReductionRedStar typing
        (svc.canonicalizeClosed term).reductionToCanonicalDevelopment := rfl

end Mettapedia.Languages.MeTTa.ElaboratedCore
