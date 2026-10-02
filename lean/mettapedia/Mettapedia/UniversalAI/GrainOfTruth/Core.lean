import Mettapedia.UniversalAI.BayesianAgents

/-!
# Countable environment classes: core types

The learning results of this directory are stated for a countable family of
environments `envs : ℕ → Environment` together with a prior on its indices.
They use nothing else about the family: in particular no oracle and no
computability assumption.

* `EnvironmentIndex`: the index of an environment in the family.
* `PriorOverClass`: positive prior weights of total mass at most one.

The class of environments computable with a reflective oracle (Leike, thesis
Chapter 7) is not defined here. Proposition 7.18 of that chapter, that the
Bayesian mixture over the class is again a member of the class, is therefore
not stated in this directory.
-/

namespace Mettapedia.UniversalAI.GrainOfTruth

open Mettapedia.UniversalAI.BayesianAgents
open scoped ENNReal NNReal

/-- A stochastic policy is an `Agent` (assigns probabilities to actions). -/
abbrev StochasticPolicy := Agent

/-- The index of an environment in a countable family `ℕ → Environment`. -/
abbrev EnvironmentIndex := ℕ

/-- A prior on the indices of a countable family of environments: every index
has positive weight and the weights sum to at most one. -/
structure PriorOverClass where
  /-- Prior weight for environment index `i`. -/
  weight : EnvironmentIndex → ℝ≥0∞
  /-- Total weight is at most 1 (a semimeasure). -/
  tsum_le_one : (∑' i, weight i) ≤ 1
  /-- Each weight is positive: every environment of the family is a candidate. -/
  positive : ∀ i, 0 < weight i

end Mettapedia.UniversalAI.GrainOfTruth
