import Mettapedia.Logic.PLNProbGuardedAdmissibility

/-!
# Probabilistically Guarded Admissibility Demo

This file instantiates the guarded admissibility object on the explicit
`A <- H -> B -> C -> D` fixture from `PLNProofCarryingContractionDemo`.

- Clean fixture: exact hard-gated chaining.
- Leaky fixture: hard gate blocks, bounded mode certifies a radius, soft mode keeps fallback explicit.
- Collider fixture: naive abduction remains blocked.
-/

namespace Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo

open Mettapedia.Logic.PLNProofCarryingContractionDemo
open Mettapedia.Logic.PLNProbGuardedAdmissibility

/-- First exact hard-gated contraction in the clean fixture. -/
def cleanHard_B : ProbGuardedDerivedQuery :=
  ofExactContraction forkStep_B_given_A

/-- Second exact hard-gated contraction in the clean fixture. -/
def cleanHard_C : ProbGuardedDerivedQuery :=
  chainWithStep cleanHard_B chainStep_C_given_A

/-- Third exact hard-gated contraction in the clean fixture. -/
def cleanHard_D : ProbGuardedDerivedQuery :=
  chainWithStep cleanHard_C chainStep_D_given_A

theorem cleanHard_B_value :
    cleanHard_B.value = some (8 / 13) := by
  simp [cleanHard_B, ofExactContraction, forkStep_B_given_A, baseProb_B_true_given_A_true_value]

theorem cleanHard_C_value :
    cleanHard_C.value = some (151 / 260) := by
  simp [cleanHard_C, chainWithStep, chainStep_C_given_A, cleanHard_B, ofExactContraction,
    baseProb_C_true_given_A_true_value]

theorem cleanHard_D_value :
    cleanHard_D.value = some (367 / 650) := by
  simp [cleanHard_D, chainWithStep, chainStep_D_given_A, cleanHard_C, chainStep_C_given_A,
    cleanHard_B, ofExactContraction, baseProb_D_true_given_A_true_value]

theorem cleanHard_D_carries_fork_sigma :
    "fork screening-off via H" ∈ cleanHard_D.sigma := by
  simp [cleanHard_D, cleanHard_C, cleanHard_B, chainWithStep, ofExactContraction,
    forkStep_B_given_A, chainStep_C_given_A, chainStep_D_given_A]

theorem cleanHard_D_carries_chain_provenance :
    "PLNEndToEnd.chainFormulaExact" ∈ cleanHard_D.provenance := by
  simp [cleanHard_D, cleanHard_C, cleanHard_B, chainWithStep, ofExactContraction,
    forkStep_B_given_A, chainStep_C_given_A, chainStep_D_given_A]

/-- Naive screened-off estimate in the leaky fixture. -/
def leakyRuleEstimate : ℚ := 133 / 221

/-- Certified radius for the leaky fixture, equal to the measured semantic deviation. -/
def leakyViolationRadius : ℚ := 213 / 4420

/-- Hard-gated exact mode blocks on the leaky fixture. -/
def leakyHardBlocked_C : ProbGuardedDerivedQuery :=
  hardGatedBlocked
    softGateStep_C_given_A.query
    (softGateStep_C_given_A.sigma ++ ["hard gate blocked: direct A -> C leak remains in the model"])
    softGateStep_C_given_A.provenance
    "direct A -> C dependence blocks the exact screened chain rewrite"

/-- Bounded mode keeps the naive estimate but carries a certified radius. -/
def leakyBounded_C : ProbGuardedDerivedQuery :=
  boundedContraction
    softGateStep_C_given_A.query
    leakyRuleEstimate
    leakyViolationRadius
    (softGateStep_C_given_A.sigma ++
      ["bounded mode: carry a conservative radius instead of pretending exact discharge"])
    (softGateStep_C_given_A.provenance ++
      ["Comparison.ErrorCharacterization.error_bound_by_max_violation"])

/-- Confidence level used for the operational soft mixture in the leaky fixture. -/
def leakyGateConfidence : ℚ := 1 - leakyViolationRadius

/-- Soft-gated operational mixture with explicit semantic fallback. -/
def leakySoft_C : ProbGuardedDerivedQuery :=
  softGuardedContraction
    softGateStep_C_given_A.query
    leakyRuleEstimate
    leakyGateConfidence
    softProb_C_true_given_A_true
    (softGateStep_C_given_A.sigma ++
      ["soft mode: operational mixture with explicit semantic fallback"])
    (softGateStep_C_given_A.provenance ++ ["explicit fallback branch"])

theorem leakyHardBlocked_C_has_no_value :
    leakyHardBlocked_C.value = none := by
  rfl

theorem leakyBounded_C_radius :
    leakyBounded_C.violationBound = some (213 / 4420) := by
  rfl

theorem leakyBounded_C_contains_exact :
    withinCertifiedBound leakyBounded_C softProb_C_true_given_A_true := by
  rw [softProb_C_true_given_A_true_value]
  norm_num [withinCertifiedBound, leakyBounded_C, boundedContraction, leakyRuleEstimate,
    leakyViolationRadius]

theorem leakySoft_C_uses_explicit_fallback :
    leakySoft_C.fallbackValue = some (13 / 20) := by
  simp [leakySoft_C, softGuardedContraction, softProb_C_true_given_A_true_value]

theorem leakySoft_C_uses_gate_confidence :
    leakySoft_C.gateConfidence = some (4207 / 4420) := by
  norm_num [leakySoft_C, softGuardedContraction, leakyGateConfidence, leakyViolationRadius]

/-- Collider negative control stays blocked in hard-gated mode. -/
def colliderHardBlocked : ProbGuardedDerivedQuery :=
  hardGatedBlocked
    colliderNegativeControl.query
    (colliderNegativeControl.sigma ++
      ["hard gate blocked: naive abduction is not an admissible collider rewrite"])
    colliderNegativeControl.provenance
    "naive abduction fails on the collider fixture"

theorem colliderHardBlocked_has_no_value :
    colliderHardBlocked.value = none := by
  rfl

theorem colliderHardBlocked_carries_no_go_provenance :
    "PLNEndToEnd.colliderNotExact" ∈ colliderHardBlocked.provenance := by
  simp [colliderHardBlocked, hardGatedBlocked, colliderNegativeControl]

theorem collider_demo_still_blocks_naive_abduction :
    colliderNaiveAbduction ≠ colliderExactProb_B_true_given_A_true := by
  norm_num [colliderNaiveAbduction, colliderExactProb_B_true_given_A_true]

end Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo
