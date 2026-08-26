import Mettapedia.UniversalAI.BadUniversalPriors

/-!
# A finite boundary for universal-agent optimality claims

The Bayes-optimality results in `BayesianAgents` are relative to a supplied
Bayesian mixture.  Pareto optimality over a sufficiently broad environment
class has a different limitation: it need not select a unique, or even locally
best, policy.

This file gives a finite witness to that distinction.  Two different
deterministic policies are both Pareto optimal over the class of all
environments at horizon two, although one is strictly worse than the other in
an explicit environment.  Thus mixture-relative maximization and broad-class
Pareto undominatedness should not be conflated.

The construction specializes the finite formalization of Theorem 18 from:

* Jan Leike and Marcus Hutter, "Bad Universal Priors and Notions of
  Optimality" (2015), arXiv:1510.05572.
-/

namespace Mettapedia.UniversalAI.OptimalityBoundary

open BayesianAgents
open BadUniversalPriors

/-- The deterministic policy that always chooses `left`. -/
noncomputable def alwaysLeft : Agent :=
  deterministicPolicy fun _ => Action.left

/-- The deterministic policy that always chooses `right`. -/
noncomputable def alwaysRight : Agent :=
  deterministicPolicy fun _ => Action.right

/-- The two policies are extensionally different already at the empty history. -/
theorem alwaysLeft_ne_alwaysRight : alwaysLeft ≠ alwaysRight := by
  intro h
  have hp := congrArg (fun π : Agent => π.policy [] Action.left) h
  simp [alwaysLeft, alwaysRight, deterministicPolicy] at hp

/-- Positive side of the boundary: both policies are Pareto undominated over
the full environment class at horizon two. -/
theorem alwaysPolicies_pareto (gamma : DiscountFactor) :
    ParetoOptimal alwaysLeft Set.univ gamma 2 ∧
      ParetoOptimal alwaysRight Set.univ gamma 2 := by
  constructor
  · exact pareto_optimality_trivial_horizon2 alwaysLeft gamma Set.univ (by simp)
  · exact pareto_optimality_trivial_horizon2 alwaysRight gamma Set.univ (by simp)

/-- Negative side of the boundary: Pareto undominatedness over the full class
does not imply that the policy is best in each member of that class. -/
theorem alwaysRight_strictly_worse_in_leftBuddy (gamma : DiscountFactor) :
    value (buddyEnvironmentNow Action.left) alwaysRight gamma [] 2 <
      value (buddyEnvironmentNow Action.left) alwaysLeft gamma [] 2 := by
  have hturn : History.agentTurn [] := by
    simp [History.agentTurn, History.wellFormed, History.actions, History.percepts]
  rw [value_buddyEnvironmentNow_horizon2 Action.left alwaysRight gamma [] hturn,
    value_buddyEnvironmentNow_horizon2 Action.left alwaysLeft gamma [] hturn]
  simp [alwaysLeft, alwaysRight, deterministicPolicy]

/-- A single theorem exposing the complete separation witness: distinct
policies, simultaneous Pareto optimality, and a strict local value ordering. -/
theorem pareto_nonselective_witness (gamma : DiscountFactor) :
    alwaysLeft ≠ alwaysRight ∧
      ParetoOptimal alwaysLeft Set.univ gamma 2 ∧
      ParetoOptimal alwaysRight Set.univ gamma 2 ∧
      value (buddyEnvironmentNow Action.left) alwaysRight gamma [] 2 <
        value (buddyEnvironmentNow Action.left) alwaysLeft gamma [] 2 := by
  exact ⟨alwaysLeft_ne_alwaysRight, alwaysPolicies_pareto gamma |>.1,
    alwaysPolicies_pareto gamma |>.2, alwaysRight_strictly_worse_in_leftBuddy gamma⟩

#print axioms alwaysLeft_ne_alwaysRight
#print axioms alwaysPolicies_pareto
#print axioms alwaysRight_strictly_worse_in_leftBuddy
#print axioms pareto_nonselective_witness

end Mettapedia.UniversalAI.OptimalityBoundary
