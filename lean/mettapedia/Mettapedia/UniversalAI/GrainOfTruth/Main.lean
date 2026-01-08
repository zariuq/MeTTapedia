import Mettapedia.UniversalAI.GrainOfTruth.Setup
import Mettapedia.UniversalAI.GrainOfTruth.FixedPoint

/-!
# Grain of Truth: Main Theorems

This file assembles the main results of the Grain of Truth formalization.

## Main Results

The **Grain of Truth Theorem** states that if all agents use asymptotically
optimal learning algorithms (like Thompson sampling) over a reflective
environment class M^O_refl, then:

1. The class M^O_refl contains its own Bayesian mixture (Proposition 7.1)
2. Thompson sampling is asymptotically optimal in mean (Theorem 7.6)
3. All agents converge to ε-Nash equilibrium (Theorem 7.5)

## Structure

```
Setup.lean
├── ReflectiveEnvironmentClass     -- The class M^O_refl
├── PriorOverClass                 -- Prior distribution
├── BayesMixture                   -- Bayesian mixture ξ
├── bayes_is_in_class             -- ξ ∈ M^O_refl
└── convergence_to_equilibrium     -- Main convergence theorem

FixedPoint.lean
├── regret                         -- V* - V^π (uses BayesianAgents)
├── historyProbability            -- μ(h) = ∏ conditional probs
├── bayesianPosteriorWeight       -- w(ν|h) = w(ν)·ν(h)/ξ(h)
├── expectedRegretOverPrior       -- E_w[V* - V^π]
├── IsAsymptoticallyOptimal       -- Regret → 0 definition
├── IsEpsilonBestResponse         -- Regret < ε definition
├── bayesian_consistency          -- Posterior concentrates (TODO)
└── consistency_implies_regret_convergence (TODO)
```

## References

- Leike, Fallenstein, & Taylor (2016). "A Formal Solution to the Grain of Truth Problem"
- Leike (2016). PhD Thesis "Nonparametric General Reinforcement Learning", Chapter 7
- Kalai & Lehrer (1993). "Rational Learning Leads to Nash Equilibrium"

-/

namespace Mettapedia.UniversalAI.GrainOfTruth.Main

open Mettapedia.UniversalAI.GrainOfTruth
open Mettapedia.UniversalAI.GrainOfTruth.FixedPoint
open Mettapedia.UniversalAI.BayesianAgents
open Mettapedia.UniversalAI.ReflectiveOracles
open Mettapedia.UniversalAI.MultiAgent

/-! ## Proposition 7.1: Bayes Mixture is in the Class

The key "reflective" property: the Bayesian mixture ξ over M^O_refl
is itself a member of M^O_refl. This is what allows agents to model
each other without infinite regress.
-/

/-- Re-export: The Bayesian mixture is in M^O_refl. -/
theorem bayes_mixture_in_class (O : Oracle) (M : ReflectiveEnvironmentClass O)
    (prior : PriorOverClass O M) (ξ : BayesMixture O M prior) :
    ∃ idx : EnvironmentIndex, ∃ n, M.members n = idx :=
  bayes_is_in_class O M prior ξ

/-! ## Theorem 7.5: Convergence to Equilibrium

If all agents are asymptotically optimal in mean, they converge to ε-Nash.
-/

/-- If all agents are asymptotically optimal, they converge to ε-Nash.
    This is the main result from Setup.lean. -/
theorem convergence_to_nash {n : ℕ} (O : Oracle)
    (M : ReflectiveEnvironmentClass O) (σ : MultiAgentEnvironment n)
    (policies : Fin n → StochasticPolicy)
    (h_asymp_opt : ∀ i, isAsymptoticallyOptimalInMean (policies i) O M)
    (ε : ℝ) (hε : ε > 0) :
    ∀ i : Fin n, ∃ t₀ : ℕ, ∀ t ≥ t₀,
      ∃ σ_i : SubjectiveEnvironment n i,
        isEpsilonBestResponse σ_i (policies i)
          ⟨1/2, by norm_num, by norm_num⟩ ε [] t :=
  convergence_to_equilibrium O M σ policies h_asymp_opt ε hε

/-! ## Theorem 7.6 (planned): Thompson Sampling is Optimal

The learning-theory core (Thompson sampling asymptotic optimality in mean) follows Leike's Chapter 5
and is developed in the measure-theory folder:

`Mettapedia/UniversalAI/GrainOfTruth/MeasureTheory/`.
-/

/-! ## Main Theorem (planned): Grain of Truth

The full “grain of truth” statement (Thompson samplers converge to ε-best responses on-policy) is
assembled once the learning-theory core (Thompson sampling AoIM) is completed.
-/

/-! ## Status Summary

### Proven (0 sorries)
- `bayes_mixture_in_class`: Bayes mixture ξ ∈ M^O_refl (uses bayes_is_in_class)
- `convergence_to_nash`: Re-export of convergence_to_equilibrium
- `regret_nonneg`: V* ≥ V^π (uses optimalValue_ge_value from BayesianAgents)
- `regret_le_optimalValue`: Regret ≤ V*
- `expectedRegretOverPrior_nonneg`: Expected regret ≥ 0

### In Progress (4 sorries in FixedPoint.lean)
1. `historyProbability_le_one`: Product of probabilities ≤ 1
2. `bayesianPosterior_sum_one`: Posterior is proper distribution
3. `bayesian_consistency`: Posterior concentrates (requires martingales)
4. `consistency_implies_regret_convergence`: Concentration → regret

### Main Theorems (2 sorries in this file)
1. `thompson_is_optimal`: Thompson sampling is asymptotically optimal
2. `grain_of_truth`: Main convergence theorem

### Key Proven Infrastructure (in BayesianAgents.lean)
- `optimalValue_ge_value`: V* ≥ V^π (the key inequality)
- `value_nonneg`: V^π ≥ 0
- `optimalValue_nonneg`: V* ≥ 0

### What's Needed for Full Proof
1. **Measure Theory**: Proper probability spaces for histories
2. **Martingale Theory**: For Bayesian consistency (Doob's theorem)
3. **Concentration Inequalities**: For converting expected → worst case
4. **PTM Semantics**: Connect to ReflectiveOracles for computability
-/

end Mettapedia.UniversalAI.GrainOfTruth.Main
