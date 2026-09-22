import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CheckingService
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.CompleteDevelopment
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services.TypedCompleteDevelopment
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics
import Mettapedia.Logic.HOL.Derivation

/-!
# HOL to the two-sort experiment: integration obligations

This file is an implementation contract, not a translator implementation.
It defines:

- what "ready" means for HOL -> two-sort integration,
- which phase is open now,
- which moves are explicitly disallowed to prevent architecture drift.

Translation must target the stated declaration-aware typing judgment.
The Boolean gates below record a development policy; their values are not
proofs of theorem transport, source faithfulness, or mathematical hosting.
This experiment is separate from the Prime candidate's host obligations.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId

open Mettapedia.Languages.MeTTa.ElaboratedCore

open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Services

/-- Readiness gates for HOL -> two-sort integration. -/
inductive HOLToTwoSortGate where
  | closedSyntaxTranslation
  | declarationTypedTranslation
  | closedTheoremTransport
  | openDerivationTransport
  | wmBridgeCoherence
deriving DecidableEq, Repr

/-- Current gate status, pinned to the live repository state. -/
def holToTwoSortGateStatus : HOLToTwoSortGate → Bool
  | .closedSyntaxTranslation => true
  | .declarationTypedTranslation => true
  | .closedTheoremTransport => false
  | .openDerivationTransport => false
  | .wmBridgeCoherence => false

theorem holToTwoSort_closedSyntax_open :
    holToTwoSortGateStatus .closedSyntaxTranslation = true := rfl

theorem holToTwoSort_declTyped_open :
    holToTwoSortGateStatus .declarationTypedTranslation = true := rfl

theorem holToTwoSort_closedTheorem_not_open :
    holToTwoSortGateStatus .closedTheoremTransport = false := rfl

theorem holToTwoSort_openDerivation_not_open :
    holToTwoSortGateStatus .openDerivationTransport = false := rfl

theorem holToTwoSort_wmBridgeCoherence_not_open :
    holToTwoSortGateStatus .wmBridgeCoherence = false := rfl

/-- Integration-phase order to keep abstraction layers aligned. -/
def holToTwoSortPhaseOrder : List String :=
  [ "freeze two-sort checking/canonicalization waist as authoritative"
  , "implement closed HOL syntax -> ScopedTerm translation targeting declaration-aware kernel terms"
  , "prove declaration-aware typing preservation for translated closed HOL terms/formulas"
  , "package translated closed terms through TwoSortCheckingBoundary.checkDeclaredConstantDelta/checkClosedTerm"
  , "only then attempt closed theorem transport (HOL derivation -> two-sort certificate)"
  , "only then attempt open-derivation transport and context-sensitive obligations"
  , "connect HOL<->WM consequences with two-sort artifacts only after theorem transport is live" ]

/-- Files that must move in lockstep for phase-1 integration. -/
def holToTwoSortPhase1TouchSet : List String :=
  [ "Mettapedia/Logic/HOL/Syntax/Type.lean"
  , "Mettapedia/Logic/HOL/Syntax/Term.lean"
  , "Mettapedia/Logic/HOL/Derivation.lean"
  , "Mettapedia/TypeTheory/Calculi/TwoSortPiSigmaId/Syntax.lean"
  , "Mettapedia/TypeTheory/Calculi/TwoSortPiSigmaId/DeclarationEnv.lean"
  , "Mettapedia/TypeTheory/Calculi/TwoSortPiSigmaId/DeclarationSemantics.lean"
  , "Mettapedia/Languages/MeTTa/Experimental/TwoSortPiSigmaId/Services/CheckingService.lean"
  , "Mettapedia/Languages/MeTTa/Experimental/TwoSortPiSigmaId/Services/CompleteDevelopment.lean"
  , "Mettapedia/Languages/MeTTa/Experimental/TwoSortPiSigmaId/Services/TypedCompleteDevelopment.lean" ]

/-- Required theorem obligations before opening closed-theorem transport. -/
def holToTwoSortPhase2Obligations : List String :=
  [ "type preservation for translated closed HOL formulas into HasTypeDecl"
  , "quote/artifact agreement for translated closed HOL formulas"
  , "declaration-environment well-formedness for translator-introduced constants"
  , "RedStarDecl preservation used by translator-side checked evaluation witnesses"
  , "bridge theorem: HOL theorem of φ implies checked two-sort certificate for encode(φ)" ]

/-- Explicit anti-drift prohibitions. -/
def holToTwoSortForbiddenMoves : List String :=
  [ "do not add HOL-specific primitives to ScopedTerm (no dedicated HOL AST constructors)"
  , "do not bypass DeclEnv/HasTypeDecl with evaluator-only semantics"
  , "do not claim theorem transport while only syntax transport is implemented"
  , "do not claim WM coherence for HOL->two-sort without explicit bridge theorem obligations" ]

/-- Contract object consumed by implementation PRs/reviews. -/
structure HOLToTwoSortIntegrationContract where
  sourceLayer : String
  targetKernelLayer : String
  targetServiceLayer : String
  gateStatus : HOLToTwoSortGate → Bool
  phaseOrder : List String
  phase1TouchSet : List String
  phase2Obligations : List String
  forbiddenMoves : List String
  phase1Region : ElaboratedRegion
  phase1Overlap : OverlapClass

def holToTwoSortIntegrationContract : HOLToTwoSortIntegrationContract :=
  { sourceLayer := "Mettapedia.Logic.HOL"
    targetKernelLayer := "Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics"
    targetServiceLayer := "Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.PatternCheckingBoundary"
    gateStatus := holToTwoSortGateStatus
    phaseOrder := holToTwoSortPhaseOrder
    phase1TouchSet := holToTwoSortPhase1TouchSet
    phase2Obligations := holToTwoSortPhase2Obligations
    forbiddenMoves := holToTwoSortForbiddenMoves
    phase1Region := twoSortCheckingBoundary.region
    phase1Overlap := twoSortCheckingBoundary.overlapClass }

theorem holToTwoSort_contract_phase1_region :
    holToTwoSortIntegrationContract.phase1Region = .twoSortKernelRegion := by
  simp [holToTwoSortIntegrationContract, twoSortCheckingBoundary_region]

theorem holToTwoSort_contract_phase1_overlap :
    holToTwoSortIntegrationContract.phase1Overlap = .artifactOnly := by
  simp [holToTwoSortIntegrationContract, twoSortCheckingBoundary_overlap]

theorem holToTwoSort_phase_order_starts_with_waist_freeze :
    holToTwoSortPhaseOrder.head? =
      some "freeze two-sort checking/canonicalization waist as authoritative" := rfl

theorem holToTwoSort_forbids_hol_ast_growth :
    holToTwoSortForbiddenMoves.head? =
      some "do not add HOL-specific primitives to ScopedTerm (no dedicated HOL AST constructors)" := rfl

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId
