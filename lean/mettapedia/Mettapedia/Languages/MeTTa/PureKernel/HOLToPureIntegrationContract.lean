import Mettapedia.Languages.MeTTa.PureCheckingService
import Mettapedia.Languages.MeTTa.PureNormalizationService
import Mettapedia.Languages.MeTTa.PureCanonicalEvaluation
import Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics
import Mettapedia.Logic.HOL.Derivation

/-!
# HOL -> Pure Integration Contract (Council-Gated)

This file is an implementation contract, not a translator implementation.
It defines:

- what "ready" means for HOL -> Pure integration,
- which phase is open now,
- which moves are explicitly disallowed to prevent architecture drift.

Council quorum rationale (high-level):

- Martin-Löf / Coquand / Dybjer / McBride / Pfenning:
  translation must target a typed kernel boundary, not ad hoc evaluator behavior.
- Brown / Buzzard / Carneiro:
  phase gates and proof obligations must be explicit and reviewable.
- Knuth / Tao / Kolmogorov:
  smallest viable next mechanism first: closed syntax transport before full proof transport.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel

open Mettapedia.Languages.MeTTa.ElaboratedCore

/-- Readiness gates for HOL -> Pure integration. -/
inductive HOLToPureGate where
  | closedSyntaxTranslation
  | declarationTypedTranslation
  | closedTheoremTransport
  | openDerivationTransport
  | wmBridgeCoherence
deriving DecidableEq, Repr

/-- Current gate status, pinned to the live repository state. -/
def holToPureGateStatus : HOLToPureGate → Bool
  | .closedSyntaxTranslation => true
  | .declarationTypedTranslation => true
  | .closedTheoremTransport => false
  | .openDerivationTransport => false
  | .wmBridgeCoherence => false

theorem holToPure_closedSyntax_open :
    holToPureGateStatus .closedSyntaxTranslation = true := rfl

theorem holToPure_declTyped_open :
    holToPureGateStatus .declarationTypedTranslation = true := rfl

theorem holToPure_closedTheorem_not_open :
    holToPureGateStatus .closedTheoremTransport = false := rfl

theorem holToPure_openDerivation_not_open :
    holToPureGateStatus .openDerivationTransport = false := rfl

theorem holToPure_wmBridgeCoherence_not_open :
    holToPureGateStatus .wmBridgeCoherence = false := rfl

/-- Integration-phase order to keep abstraction layers aligned. -/
def holToPurePhaseOrder : List String :=
  [ "freeze Pure checking/canonicalization waist as authoritative"
  , "implement closed HOL syntax -> PureTm translation targeting declaration-aware kernel terms"
  , "prove declaration-aware typing preservation for translated closed HOL terms/formulas"
  , "package translated closed terms through PureCheckingBoundary.checkDeclaredConstantDelta/checkClosedTerm"
  , "only then attempt closed theorem transport (HOL derivation -> Pure certificate)"
  , "only then attempt open-derivation transport and context-sensitive obligations"
  , "connect HOL<->WM consequences with Pure artifacts only after theorem transport is live" ]

/-- Files that must move in lockstep for phase-1 integration. -/
def holToPurePhase1TouchSet : List String :=
  [ "Mettapedia/Logic/HOL/Syntax/Type.lean"
  , "Mettapedia/Logic/HOL/Syntax/Term.lean"
  , "Mettapedia/Logic/HOL/Derivation.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/Syntax.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationEnv.lean"
  , "Mettapedia/Languages/MeTTa/PureKernel/DeclarationSemantics.lean"
  , "Mettapedia/Languages/MeTTa/PureCheckingService.lean"
  , "Mettapedia/Languages/MeTTa/PureNormalizationService.lean"
  , "Mettapedia/Languages/MeTTa/PureCanonicalEvaluation.lean" ]

/-- Required theorem obligations before opening closed-theorem transport. -/
def holToPurePhase2Obligations : List String :=
  [ "type preservation for translated closed HOL formulas into HasTypeDecl"
  , "quote/artifact agreement for translated closed HOL formulas"
  , "declaration-environment well-formedness for translator-introduced constants"
  , "RedStarDecl preservation used by translator-side checked evaluation witnesses"
  , "bridge theorem: HOL theorem of φ implies checked Pure certificate for encode(φ)" ]

/-- Explicit anti-drift prohibitions. -/
def holToPureForbiddenMoves : List String :=
  [ "do not add HOL-specific primitives to PureTm (no dedicated HOL AST constructors)"
  , "do not bypass DeclEnv/HasTypeDecl with evaluator-only semantics"
  , "do not claim theorem transport while only syntax transport is implemented"
  , "do not claim WM coherence for HOL->Pure without explicit bridge theorem obligations" ]

/-- Contract object consumed by implementation PRs/reviews. -/
structure HOLToPureIntegrationContract where
  sourceLayer : String
  targetKernelLayer : String
  targetServiceLayer : String
  gateStatus : HOLToPureGate → Bool
  phaseOrder : List String
  phase1TouchSet : List String
  phase2Obligations : List String
  forbiddenMoves : List String
  phase1Region : ElaboratedRegion
  phase1Overlap : OverlapClass

def holToPureIntegrationContract : HOLToPureIntegrationContract :=
  { sourceLayer := "Mettapedia.Logic.HOL"
    targetKernelLayer := "Mettapedia.Languages.MeTTa.PureKernel.DeclarationSemantics"
    targetServiceLayer := "Mettapedia.Languages.MeTTa.PureCheckingBoundary"
    gateStatus := holToPureGateStatus
    phaseOrder := holToPurePhaseOrder
    phase1TouchSet := holToPurePhase1TouchSet
    phase2Obligations := holToPurePhase2Obligations
    forbiddenMoves := holToPureForbiddenMoves
    phase1Region := pureCheckingBoundary.region
    phase1Overlap := pureCheckingBoundary.overlapClass }

theorem holToPure_contract_phase1_region :
    holToPureIntegrationContract.phase1Region = .pureKernelRegion := by
  simp [holToPureIntegrationContract, pureCheckingBoundary_region]

theorem holToPure_contract_phase1_overlap :
    holToPureIntegrationContract.phase1Overlap = .artifactOnly := by
  simp [holToPureIntegrationContract, pureCheckingBoundary_overlap]

theorem holToPure_phase_order_starts_with_waist_freeze :
    holToPurePhaseOrder.head? =
      some "freeze Pure checking/canonicalization waist as authoritative" := rfl

theorem holToPure_forbids_hol_ast_growth :
    holToPureForbiddenMoves.head? =
      some "do not add HOL-specific primitives to PureTm (no dedicated HOL AST constructors)" := rfl

end Mettapedia.Languages.MeTTa.PureKernel
