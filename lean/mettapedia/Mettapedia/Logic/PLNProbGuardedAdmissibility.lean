import Mettapedia.Logic.PLNProofCarryingContractionDemo
import Mettapedia.Logic.Comparison.ErrorCharacterization

/-!
# Probabilistically Guarded Admissibility

This module adds a minimal carried-object layer for guarded PLN-style chaining.

- The BN / factor-graph semantics remain the truthmaker.
- Exact rewrites stay hard-gated and theorem-backed.
- Bounded mode carries an explicit certified radius instead of a naked point.
- Soft mode is an operational mixture with explicit fallback, not automatic semantics.

The design is intentionally small and demo-oriented.  It extends the existing
proof-carrying contraction example rather than replacing it.
-/

namespace Mettapedia.Logic.PLNProbGuardedAdmissibility

open Mettapedia.Logic.PLNProofCarryingContractionDemo

/-- Operational mode for a guarded derived query. -/
inductive GuardMode where
  | hardGatedExact
  | localExactFallback
  | higherOrderSemanticGuarded
  | boundedViolation
  | softGuardedMixture
  deriving DecidableEq, Repr

/-- Whether a guarded query actually fires or is blocked. -/
inductive GuardStatus where
  | derived
  | blocked
  deriving DecidableEq, Repr

/-- A cached derived query answer with explicit carried context. -/
structure ProbGuardedDerivedQuery where
  query : String
  value : Option ℚ
  sigma : List String
  provenance : List String
  mode : GuardMode
  status : GuardStatus
  gateConfidence : Option ℚ := none
  violationBound : Option ℚ := none
  fallbackValue : Option ℚ := none
  blockedReason : Option String := none
  deriving Repr

/-- Hard-gated exact result from a proof-carrying contraction step. -/
def ofExactContraction (step : ProofCarryingContraction) : ProbGuardedDerivedQuery where
  query := step.query
  value := some step.exactValue
  sigma := step.sigma
  provenance := step.provenance
  mode := .hardGatedExact
  status := .derived

/-- Hard-gated blocked result when Sigma is not discharged. -/
def hardGatedBlocked
    (query : String)
    (sigma provenance : List String)
    (reason : String) : ProbGuardedDerivedQuery where
  query := query
  value := none
  sigma := sigma
  provenance := provenance
  mode := .hardGatedExact
  status := .blocked
  blockedReason := some reason

/-- Bounded result: return an estimate together with an explicit radius. -/
def boundedContraction
    (query : String)
    (estimate bound : ℚ)
    (sigma provenance : List String) : ProbGuardedDerivedQuery where
  query := query
  value := some estimate
  sigma := sigma
  provenance := provenance
  mode := .boundedViolation
  status := .derived
  violationBound := some bound

/-- Operational soft-gated mixture with explicit fallback. -/
def softGuardedContraction
    (query : String)
    (estimate gateConfidence fallback : ℚ)
    (sigma provenance : List String) : ProbGuardedDerivedQuery where
  query := query
  value := some (gateConfidence * estimate + (1 - gateConfidence) * fallback)
  sigma := sigma
  provenance := provenance
  mode := .softGuardedMixture
  status := .derived
  gateConfidence := some gateConfidence
  fallbackValue := some fallback

/-- Chaining preserves previously carried Sigma and provenance. -/
def chainWithStep
    (prev : ProbGuardedDerivedQuery)
    (step : ProofCarryingContraction) : ProbGuardedDerivedQuery where
  query := step.query
  value := some step.exactValue
  sigma := prev.sigma ++ step.sigma
  provenance := prev.provenance ++ step.provenance
  mode := .hardGatedExact
  status := .derived

/-- Conservative lower endpoint when a bounded estimate is available. -/
def certifiedLower (result : ProbGuardedDerivedQuery) : Option ℚ :=
  match result.value, result.violationBound with
  | some estimate, some bound => some (estimate - bound)
  | _, _ => none

/-- Conservative upper endpoint when a bounded estimate is available. -/
def certifiedUpper (result : ProbGuardedDerivedQuery) : Option ℚ :=
  match result.value, result.violationBound with
  | some estimate, some bound => some (estimate + bound)
  | _, _ => none

/-- The exact value lies within the explicitly carried radius. -/
def withinCertifiedBound (result : ProbGuardedDerivedQuery) (exact : ℚ) : Prop :=
  match result.value, result.violationBound with
  | some estimate, some bound => |exact - estimate| ≤ bound
  | _, _ => False

/-- Soft-gated value as a standalone mixture term. -/
def softGuardedMixtureValue (gateConfidence estimate fallback : ℚ) : ℚ :=
  gateConfidence * estimate + (1 - gateConfidence) * fallback

theorem softGuardedMixtureValue_gate_one (estimate fallback : ℚ) :
    softGuardedMixtureValue 1 estimate fallback = estimate := by
  simp [softGuardedMixtureValue]

theorem softGuardedMixtureValue_gate_zero (estimate fallback : ℚ) :
    softGuardedMixtureValue 0 estimate fallback = fallback := by
  simp [softGuardedMixtureValue]

theorem chainWithStep_carries_sigma
    {prev : ProbGuardedDerivedQuery}
    {step : ProofCarryingContraction}
    {item : String}
    (h : item ∈ prev.sigma) :
    item ∈ (chainWithStep prev step).sigma := by
  simp [chainWithStep, h]

theorem chainWithStep_carries_provenance
    {prev : ProbGuardedDerivedQuery}
    {step : ProofCarryingContraction}
    {item : String}
    (h : item ∈ prev.provenance) :
    item ∈ (chainWithStep prev step).provenance := by
  simp [chainWithStep, h]

theorem hardGatedBlocked_has_no_value
    (query : String)
    (sigma provenance : List String)
    (reason : String) :
    (hardGatedBlocked query sigma provenance reason).value = none := by
  rfl

theorem ofExactContraction_has_exact_mode
    (step : ProofCarryingContraction) :
    (ofExactContraction step).mode = .hardGatedExact := by
  rfl

theorem boundedContraction_has_radius
    (query : String)
    (estimate bound : ℚ)
    (sigma provenance : List String) :
    (boundedContraction query estimate bound sigma provenance).violationBound = some bound := by
  rfl

theorem softGuardedContraction_exposes_fallback
    (query : String)
    (estimate gateConfidence fallback : ℚ)
    (sigma provenance : List String) :
    (softGuardedContraction query estimate gateConfidence fallback sigma provenance).fallbackValue =
      some fallback := by
  rfl

end Mettapedia.Logic.PLNProbGuardedAdmissibility
