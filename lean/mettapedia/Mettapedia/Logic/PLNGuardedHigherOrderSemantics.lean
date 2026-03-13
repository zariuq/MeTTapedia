import Mettapedia.Logic.PLNProbGuardedAdmissibility

/-!
# Guarded Higher-Order Semantics

This module adds a thin semantic bridge over `PLNProbGuardedAdmissibility`.

- `ProbGuardedDerivedQuery` remains the carried query object.
- `SemanticProbGuardedQuery` adds an explicit semantic-status layer.
- Higher-order guardedness is represented by an explicit finite regime model over:
  exact admissibility, bounded violation, and fallback.

This keeps the exact BN truthmaker primary while allowing some guarded outputs to
be semantic in an expanded model, rather than merely operational scores.
-/

namespace Mettapedia.Logic.PLNGuardedHigherOrderSemantics

open Mettapedia.Logic.PLNProbGuardedAdmissibility

/-- Public semantic-status labels for guarded queries. -/
inductive GuardSemanticStatus where
  | theoremCertifiedExact
  | higherOrderSemanticGuarded
  | operationalControlOnly
  deriving DecidableEq, Repr

/-- Explicit latent regimes for guarded admissibility. -/
inductive GuardRegime where
  | exactAdmissible
  | boundedViolation
  | fallbackRequired
  deriving DecidableEq, Repr

/-- Finite regime weights for a higher-order admissibility model. -/
structure GuardRegimeWeights where
  exactMass : ℚ
  boundedMass : ℚ
  fallbackMass : ℚ
  deriving DecidableEq, Repr

/-- Validity conditions for a finite higher-order regime model. -/
def ValidGuardRegimeWeights (weights : GuardRegimeWeights) : Prop :=
  0 ≤ weights.exactMass ∧
    0 ≤ weights.boundedMass ∧
    0 ≤ weights.fallbackMass ∧
    weights.exactMass + weights.boundedMass + weights.fallbackMass = 1

/-- Explicit higher-order payload: regime weights plus branch values. -/
structure HigherOrderGuardPayload where
  weights : GuardRegimeWeights
  exactBranchValue : ℚ
  boundedBranchValue : ℚ
  fallbackBranchValue : ℚ
  deriving DecidableEq, Repr

/-- Flattened first-order value induced by the finite higher-order regime model. -/
def higherOrderSemanticValue (payload : HigherOrderGuardPayload) : ℚ :=
  payload.weights.exactMass * payload.exactBranchValue
    + payload.weights.boundedMass * payload.boundedBranchValue
    + payload.weights.fallbackMass * payload.fallbackBranchValue

/-- Confidence mass assigned to admissible-or-bounded regimes. -/
def higherOrderGuardConfidence (payload : HigherOrderGuardPayload) : ℚ :=
  payload.weights.exactMass + payload.weights.boundedMass

/-- Conservative radius around the flattened value covering every regime branch. -/
def higherOrderSemanticRadius (payload : HigherOrderGuardPayload) : ℚ :=
  max
    (|higherOrderSemanticValue payload - payload.exactBranchValue|)
    (max
      (|higherOrderSemanticValue payload - payload.boundedBranchValue|)
      (|higherOrderSemanticValue payload - payload.fallbackBranchValue|))

/-- A guarded query together with an explicit semantic-status tag. -/
structure SemanticProbGuardedQuery extends ProbGuardedDerivedQuery where
  semanticStatus : GuardSemanticStatus
  higherOrderGuard : Option HigherOrderGuardPayload := none
  deriving Repr

/-- Lift an exact or blocked theorem-backed branch into the semantic-status layer. -/
def liftTheoremExact (base : ProbGuardedDerivedQuery) : SemanticProbGuardedQuery where
  toProbGuardedDerivedQuery := base
  semanticStatus := .theoremCertifiedExact

/-- Lift a non-exact carried object into the operational-control layer. -/
def liftOperational (base : ProbGuardedDerivedQuery) : SemanticProbGuardedQuery where
  toProbGuardedDerivedQuery := base
  semanticStatus := .operationalControlOnly

/-- Exact local fallback against the semantic truthmaker. -/
def exactFallbackContraction
    (query : String)
    (exactValue : ℚ)
    (sigma provenance : List String) : SemanticProbGuardedQuery where
  toProbGuardedDerivedQuery := {
    query := query
    value := some exactValue
    sigma := sigma
    provenance := provenance ++ ["local exact fallback against the BN truthmaker"]
    mode := .localExactFallback
    status := .derived
  }
  semanticStatus := .theoremCertifiedExact

/-- Higher-order semantic guarded contraction from an explicit regime model. -/
def higherOrderSemanticContraction
    (query : String)
    (payload : HigherOrderGuardPayload)
    (_hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String) : SemanticProbGuardedQuery where
  toProbGuardedDerivedQuery := {
    query := query
    value := some (higherOrderSemanticValue payload)
    sigma := sigma
    provenance := provenance ++ ["finite higher-order regime model over admissibility"]
    mode := .higherOrderSemanticGuarded
    status := .derived
    gateConfidence := some (higherOrderGuardConfidence payload)
    violationBound := some (higherOrderSemanticRadius payload)
    fallbackValue := some payload.fallbackBranchValue
  }
  semanticStatus := .higherOrderSemanticGuarded
  higherOrderGuard := some payload

theorem liftTheoremExact_has_exact_status
    (base : ProbGuardedDerivedQuery) :
    (liftTheoremExact base).semanticStatus = .theoremCertifiedExact := by
  rfl

theorem liftOperational_has_operational_status
    (base : ProbGuardedDerivedQuery) :
    (liftOperational base).semanticStatus = .operationalControlOnly := by
  rfl

theorem exactFallbackContraction_has_fallback_mode
    (query : String)
    (exactValue : ℚ)
    (sigma provenance : List String) :
    (exactFallbackContraction query exactValue sigma provenance).mode = .localExactFallback := by
  rfl

theorem higherOrderSemanticContraction_has_semantic_status
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String) :
    (higherOrderSemanticContraction query payload hweights sigma provenance).semanticStatus =
      .higherOrderSemanticGuarded := by
  rfl

theorem higherOrderSemanticContraction_records_payload
    (query : String)
    (payload : HigherOrderGuardPayload)
    (hweights : ValidGuardRegimeWeights payload.weights)
    (sigma provenance : List String) :
    (higherOrderSemanticContraction query payload hweights sigma provenance).higherOrderGuard =
      some payload := by
  rfl

theorem higherOrderSemanticRadius_covers_exact_branch
    (payload : HigherOrderGuardPayload) :
    |higherOrderSemanticValue payload - payload.exactBranchValue| ≤
      higherOrderSemanticRadius payload := by
  unfold higherOrderSemanticRadius
  exact le_max_left _ _

theorem higherOrderSemanticRadius_covers_bounded_branch
    (payload : HigherOrderGuardPayload) :
    |higherOrderSemanticValue payload - payload.boundedBranchValue| ≤
      higherOrderSemanticRadius payload := by
  unfold higherOrderSemanticRadius
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem higherOrderSemanticRadius_covers_fallback_branch
    (payload : HigherOrderGuardPayload) :
    |higherOrderSemanticValue payload - payload.fallbackBranchValue| ≤
      higherOrderSemanticRadius payload := by
  unfold higherOrderSemanticRadius
  exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem higherOrderGuardConfidence_eq_exact_plus_bounded
    (payload : HigherOrderGuardPayload) :
    higherOrderGuardConfidence payload =
      payload.weights.exactMass + payload.weights.boundedMass := by
  rfl

end Mettapedia.Logic.PLNGuardedHigherOrderSemantics
