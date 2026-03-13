import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.PureKernel.HOLToPureIntegrationContract
import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Logic.HOL.LogicalInduction.Code

/-!
# HOL Logical-Induction Codes and the Pure Checking Boundary

This module records the current Pure-facing integration shape for the
logical-induction-ready HOL belief layer.

Following Garrabrant, Benson-Tilsen, Critch, Soares, and Taylor,
*Logical Induction*, arXiv:1609.03543v5 (2020), future higher-order logical
uncertainty will eventually want canonical coding/quoting of closed formulas.

In the current repository state, theorem transport into the MeTTa Pure kernel is
**not** open yet.  What *is* open, by the council-gated contract, is the
artifact-only phase-1 boundary:

- encode closed HOL formulas into closed Pure terms,
- check them through the declaration-aware Pure checking boundary,
- and preserve quoted-artifact agreement.

This file therefore defines the exact artifact-level interface expected from any
future HOL-to-Pure encoder, while staying strictly inside the open contract
gates.
-/

namespace Mettapedia.Logic.HOL.LogicalInduction

open Mettapedia.Logic.HOL
open Mettapedia.Languages.MeTTa.ElaboratedCore
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Typing
open Mettapedia.Languages.MeTTa.PureKernel
open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Artifact-level Pure encoding data for one closed HOL formula code. -/
structure ClosedFormulaArtifactEncoding (Const : Ty Base → Type v) where
  formula : ClosedFormulaCode Const
  term : PureTm 0
  claimedType : PureTm 0
  typing : HasType .nil term claimedType

namespace ClosedFormulaArtifactEncoding

/-- Canonical checked certificate obtained from the current Pure checking boundary. -/
def checked
    (enc : ClosedFormulaArtifactEncoding Const) :
    CheckedPureCertificate :=
  pureCheckingBoundary.checkClosedTerm enc.term enc.claimedType enc.typing

theorem checked_term
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.term = enc.term := by
  exact pureCheckingBoundary.checkClosedTerm_term enc.term enc.claimedType enc.typing

theorem checked_typing
    (enc : ClosedFormulaArtifactEncoding Const) :
    HasType .nil enc.checked.term enc.claimedType := by
  simpa [checked] using enc.checked.emptyContextTyping

theorem checked_quoteAgreement
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.artifact.pattern = quoteClosedTm enc.term := by
  simpa [checked, checked_term] using
    pureCheckingBoundary.checkClosedTerm_quoteAgreement enc.term enc.claimedType enc.typing

theorem checked_region_pureKernel
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.region = .pureKernelRegion := rfl

theorem checked_overlap_artifactOnly
    (enc : ClosedFormulaArtifactEncoding Const) :
    enc.checked.overlapClass = .artifactOnly := rfl

end ClosedFormulaArtifactEncoding

/-- A future HOL-to-Pure encoder should provide this artifact-level data for
each closed HOL formula code.  The present file does not yet implement such an
encoder; it fixes the boundary that any implementation must satisfy. -/
structure ClosedFormulaEncoder (Const : Ty Base → Type v) where
  encode : ClosedFormulaCode Const → ClosedFormulaArtifactEncoding Const

/-- Phase-1 compatibility with the current Pure contract: every encoded closed
formula yields an artifact-only checked Pure certificate. -/
def Phase1Compatible
    (E : ClosedFormulaEncoder Const) : Prop :=
  ∀ φ : ClosedFormulaCode Const,
    let enc := E.encode φ
    enc.checked.region = .pureKernelRegion ∧
      enc.checked.overlapClass = .artifactOnly ∧
      enc.checked.artifact.pattern = quoteClosedTm enc.term

theorem phase1Compatible_of_encoder
    (E : ClosedFormulaEncoder Const) :
    Phase1Compatible (Const := Const) E := by
  intro φ
  dsimp [Phase1Compatible]
  refine ⟨?_, ?_, ?_⟩
  · exact (E.encode φ).checked_region_pureKernel
  · exact (E.encode φ).checked_overlap_artifactOnly
  · exact (E.encode φ).checked_quoteAgreement

theorem pure_phase1_closedSyntax_open :
    Mettapedia.Languages.MeTTa.PureKernel.holToPureGateStatus
      .closedSyntaxTranslation = true :=
  Mettapedia.Languages.MeTTa.PureKernel.holToPure_closedSyntax_open

theorem pure_phase1_declTyped_open :
    Mettapedia.Languages.MeTTa.PureKernel.holToPureGateStatus
      .declarationTypedTranslation = true :=
  Mettapedia.Languages.MeTTa.PureKernel.holToPure_declTyped_open

theorem pure_phase2_theoremTransport_not_open :
    Mettapedia.Languages.MeTTa.PureKernel.holToPureGateStatus
      .closedTheoremTransport = false :=
  Mettapedia.Languages.MeTTa.PureKernel.holToPure_closedTheorem_not_open

end Mettapedia.Logic.HOL.LogicalInduction
