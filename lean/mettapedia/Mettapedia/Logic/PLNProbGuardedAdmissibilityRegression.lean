import Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo

/-!
# Probabilistically Guarded Admissibility Regression Surface

This file exposes a small stable surface for the clean, leaky, and collider
guarded-admissibility demos.
-/

namespace Mettapedia.Logic.PLNProbGuardedAdmissibilityRegression

open Mettapedia.Logic.PLNProbGuardedAdmissibility
open Mettapedia.Logic.PLNProbGuardedAdmissibilityDemo
open Mettapedia.Logic.PLNProofCarryingContractionDemo

abbrev probGuard_clean_B_given_A : ProbGuardedDerivedQuery := cleanHard_B
abbrev probGuard_clean_C_given_A : ProbGuardedDerivedQuery := cleanHard_C
abbrev probGuard_clean_D_given_A : ProbGuardedDerivedQuery := cleanHard_D
abbrev probGuard_leaky_blocked_C_given_A : ProbGuardedDerivedQuery := leakyHardBlocked_C
abbrev probGuard_leaky_bounded_C_given_A : ProbGuardedDerivedQuery := leakyBounded_C
abbrev probGuard_leaky_soft_C_given_A : ProbGuardedDerivedQuery := leakySoft_C
abbrev probGuard_collider_blocked_B_given_A : ProbGuardedDerivedQuery := colliderHardBlocked

theorem probGuard_clean_B_given_A_value :
    probGuard_clean_B_given_A.value = some (8 / 13) := by
  exact cleanHard_B_value

theorem probGuard_clean_C_given_A_value :
    probGuard_clean_C_given_A.value = some (151 / 260) := by
  exact cleanHard_C_value

theorem probGuard_clean_D_given_A_value :
    probGuard_clean_D_given_A.value = some (367 / 650) := by
  exact cleanHard_D_value

theorem probGuard_clean_D_given_A_carries_sigma :
    "fork screening-off via H" ∈ probGuard_clean_D_given_A.sigma := by
  exact cleanHard_D_carries_fork_sigma

theorem probGuard_leaky_blocked_C_given_A_is_blocked :
    probGuard_leaky_blocked_C_given_A.value = none := by
  exact leakyHardBlocked_C_has_no_value

theorem probGuard_leaky_bounded_C_given_A_contains_exact :
    withinCertifiedBound probGuard_leaky_bounded_C_given_A softProb_C_true_given_A_true := by
  exact leakyBounded_C_contains_exact

theorem probGuard_leaky_soft_C_given_A_has_fallback :
    probGuard_leaky_soft_C_given_A.fallbackValue = some (13 / 20) := by
  exact leakySoft_C_uses_explicit_fallback

theorem probGuard_collider_blocked_B_given_A_is_blocked :
    probGuard_collider_blocked_B_given_A.value = none := by
  exact colliderHardBlocked_has_no_value

theorem probGuard_collider_blocked_B_given_A_has_no_go :
    "PLNEndToEnd.colliderNotExact" ∈ probGuard_collider_blocked_B_given_A.provenance := by
  exact colliderHardBlocked_carries_no_go_provenance

end Mettapedia.Logic.PLNProbGuardedAdmissibilityRegression
