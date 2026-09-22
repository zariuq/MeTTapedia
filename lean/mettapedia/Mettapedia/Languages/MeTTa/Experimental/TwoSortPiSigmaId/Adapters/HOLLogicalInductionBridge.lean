import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CheckingService
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.HOLToTwoSortIntegrationContract
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
import Mettapedia.Logic.HOL.LogicalInduction.Code

/-!
# HOL Logical-Induction Codes and the two-sort Checking Boundary

This module records the current two-sort-facing integration shape for the
logical-induction-ready HOL belief layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), future higher-order logical
uncertainty will eventually want canonical coding/quoting of closed formulas.

In the current repository state, theorem transport into the the two-sort experiment kernel is
**not** open yet.  What *is* open, by the explicit integration contract, is the
artifact-only phase-1 boundary:

- encode closed HOL formulas into closed two-sort terms,
- check them through the declaration-aware two-sort checking boundary,
- and preserve quoted-artifact agreement.

This file therefore defines the exact artifact-level interface expected from any
future HOL-to-two-sort encoder, while staying strictly inside the open contract
gates.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.HOLLogicalInductionBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.LogicalInduction
open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Artifact-level two-sort encoding data for one closed HOL formula code. -/
structure ClosedFormulaArtifactEncoding (Const : Ty Base → Type v) where
  formula : ClosedFormulaCode Const
  term : ScopedTerm 0
  claimedType : ScopedTerm 0
  typing : HasType .nil term claimedType

namespace ClosedFormulaArtifactEncoding

/-- Canonical checked certificate obtained from the current two-sort checking boundary. -/
def checked
    (enc : ClosedFormulaArtifactEncoding Const) :
    CheckedTwoSortCertificate :=
  twoSortCheckingBoundary.checkClosedTerm enc.term enc.claimedType enc.typing

theorem checked_term
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.term = enc.term := by
  exact twoSortCheckingBoundary.checkClosedTerm_term enc.term enc.claimedType enc.typing

theorem checked_typing
    (enc : ClosedFormulaArtifactEncoding Const) :
    HasType .nil enc.checked.term enc.claimedType := by
  simpa [checked] using
    twoSortCheckingBoundary.checkClosedTerm_typing enc.term enc.claimedType enc.typing

theorem checked_quoteAgreement
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.artifact.pattern = quoteClosedTm enc.term := by
  simpa [checked, twoSortCheckingBoundary.checkClosedTerm_term enc.term enc.claimedType enc.typing] using
    twoSortCheckingBoundary.checkClosedTerm_quoteAgreement enc.term enc.claimedType enc.typing

theorem checked_region_twoSortKernel
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.region = .twoSortKernelRegion := rfl

theorem checked_overlap_artifactOnly
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.overlapClass = .artifactOnly := rfl

end ClosedFormulaArtifactEncoding

/-- A future HOL-to-two-sort encoder should provide this artifact-level data for
each closed HOL formula code.  The present file does not yet implement such an
encoder; it fixes the boundary that any implementation must satisfy. -/
structure ClosedFormulaEncoder (Const : Ty Base → Type v) where
  encode : ClosedFormulaCode Const → ClosedFormulaArtifactEncoding Const

/-- Phase-1 compatibility with the current two-sort contract: every encoded closed
formula yields an artifact-only checked two-sort certificate. -/
def Phase1Compatible
    (E : ClosedFormulaEncoder Const) : Prop :=
  ∀ φ : ClosedFormulaCode Const,
    let enc := E.encode φ
    enc.checked.region = .twoSortKernelRegion ∧
      enc.checked.overlapClass = .artifactOnly ∧
      enc.checked.artifact.pattern = quoteClosedTm enc.term

theorem phase1Compatible_of_encoder
    (E : ClosedFormulaEncoder Const) :
    Phase1Compatible (Const := Const) E := by
  intro φ
  dsimp [Phase1Compatible]
  refine ⟨?_, ?_, ?_⟩
  · exact (E.encode φ).checked_region_twoSortKernel
  · exact (E.encode φ).checked_overlap_artifactOnly
  · exact (E.encode φ).checked_quoteAgreement

theorem twoSort_phase1_closedSyntax_open :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.holToTwoSortGateStatus
      .closedSyntaxTranslation = true :=
  Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.holToTwoSort_closedSyntax_open

theorem twoSort_phase1_declTyped_open :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.holToTwoSortGateStatus
      .declarationTypedTranslation = true :=
  Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.holToTwoSort_declTyped_open

theorem twoSort_phase2_theoremTransport_not_open :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.holToTwoSortGateStatus
      .closedTheoremTransport = false :=
  Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.holToTwoSort_closedTheorem_not_open

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.HOLLogicalInductionBridge
