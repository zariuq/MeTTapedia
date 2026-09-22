import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CompleteDevelopment
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.SubjectReduction
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory

/-!
# Typed complete development for the two-sort experiment

One-pass complete development preserving the permissive typing judgment of
`TwoSortPiSigmaId`. The output need not be a normal form.

This module intentionally stays inside the purified kernel boundary:

- closed `ScopedTerm` inputs,
- closed typing proofs,
- canonicalization through `cdev`,
- output typing by subject reduction,
- quoted artifact and profile-theory consequences.

It does **not** reintroduce the archived prototype parser, fuel evaluator, or
CLI tooling.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services

open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.SubjectReduction
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory

theorem subjectReductionRedStar {Γ : Ctx n} {t u A : ScopedTerm n}
    (ht : HasType Γ t A) (h : RedStar t u) :
    HasType Γ u A := by
  induction h generalizing A with
  | refl =>
      simpa using ht
  | tail htu huv ih =>
      exact subject_reduction (ih ht) huv

/-- Checked canonicalization of a closed two-sort term through the live canonical
development service. -/
structure CheckedCanonicalEvaluation where
  input : ScopedTerm 0
  claimedType : ScopedTerm 0
  inputTyping : HasType .nil input claimedType
  canonical : CanonicalClosedTwoSortTerm
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
    TwoSortProfileTheoryStepStar
      (quoteClosedTm result.input)
      (quoteClosedTm result.canonical.canonicalDevelopment) := by
  have hred : RedStar result.input result.canonical.canonicalDevelopment := by
    simpa [result.canonicalInput_eq] using
      result.canonical.reductionToCanonicalDevelopment
  exact twoSortTheoryStepStar_sound_twoSortProfileTheoryStepStar_quoteClosed hinst0 hcompat0 hred

def TwoSortCheckingBoundary.checkAndCanonicalizeClosedTerm
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0)
    (claimedType : ScopedTerm 0)
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

theorem TwoSortCheckingBoundary.checkAndCanonicalizeClosedTerm_preserves_type
    (svc : TwoSortCheckingBoundary)
    (term : ScopedTerm 0)
    (claimedType : ScopedTerm 0)
    (typing : HasType .nil term claimedType) :
    (svc.checkAndCanonicalizeClosedTerm term claimedType typing).outputTyping =
      subjectReductionRedStar typing
        (svc.canonicalizeClosed term).reductionToCanonicalDevelopment := rfl

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services
