import Mettapedia.ProbabilityTheory.BeliefFunctions.Basic

/-!
# Dempster-Shafer Belief Functions

This module provides a formalization of Dempster-Shafer theory as a special case
of imprecise probability.

## Files

- `Basic.lean`: Core definitions (mass functions, belief, plausibility, Dempster's rule)

## Connection to Other Modules

- `ImpreciseProbability/`: D-S belief functions are special lower probabilities
- `KnuthSkilling/`: K&S separation forces D-S to collapse to standard probability
- `Unified.lean`: D-S sits at the (imprecise, commutative) vertex

## References

- Shafer, G. "A Mathematical Theory of Evidence" (1976)
- Dempster, A.P. "Upper and Lower Probabilities" (1967)
-/
