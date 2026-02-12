import Mettapedia.Logic.MarkovDeFinettiHardMomentFunctional
import Mettapedia.Logic.MarkovDeFinettiHardRepresentability
import Mettapedia.Logic.MarkovDeFinettiRecurrence
import Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge

/-!
# Markov de Finetti (Hard Direction) — Finite Satisfiability Core

`Mettapedia.Logic.MarkovDeFinettiHard` reduces the Diaconis–Freedman representation theorem
(Markov exchangeability **with recurrence** ⇒ mixture of Markov chains) to a compactness
argument over the compact parameter space `MarkovParam k`.

The *only* remaining nontrivial content is the **finite satisfiability** statement:

> for every finite family of evidence constraints, there exists a probability measure `π` on
> `MarkovParam k` satisfying them simultaneously.

This file isolates that statement as a single theorem, so the main theorem file can remain a thin
wrapper around the compactness reduction.

Once this theorem is proven, `markovDeFinetti_hard` becomes sorry-free.
-/

noncomputable section

namespace Mettapedia.Logic

open scoped Classical BigOperators

namespace MarkovDeFinettiHard

open MeasureTheory

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.UniversalPrediction.FiniteAlphabet
open Mettapedia.Logic.UniversalPrediction.MarkovExchangeabilityBridge
open Mettapedia.Logic.MarkovDeFinettiRecurrence

variable {k : ℕ}

open MarkovDeFinettiHard

/-!
## Finite satisfiability of the evidence moment constraints

The constraints are stated using the evidence basis from `MarkovDeFinettiEvidenceBasis.lean`:

* `wμ μ n e` is the total mass of the evidence class `(n,e)` under the environment `μ`,
* `Wnn n e` is the corresponding continuous `ℝ≥0`-valued evidence polynomial on `MarkovParam k`,
* `constraintSet μ n e` is the closed subset of `ProbabilityMeasure (MarkovParam k)` enforcing
  `wμ μ n e = ∫ Wnn n e dπ`.

The hard direction asks for a single `π` satisfying *all* constraints; compactness reduces this to
the finite-intersection property below.
-/

theorem finite_constraints_nonempty
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ u : Finset (ℕ × MarkovState k),
      (⋂ p ∈ u, MarkovDeFinettiHard.constraintSet (k := k) μ p.1 p.2).Nonempty := by
  -- TODO (Diaconis–Freedman 1980, hard direction; finite satisfiability core):
  --
  -- Prove that any finite family of evidence constraints is satisfiable by some probability
  -- measure on the compact parameter space `MarkovParam k`.
  --
  -- This is the genuine new content beyond the (already formalized) compactness reduction in
  -- `MarkovDeFinettiHardRepresentability.lean`.
  --
  -- Suggested attack routes (to be formalized, not taken as axioms):
  -- * Convex-analytic: show the moment vector lies in the compact convex hull of evaluations and
  --   apply a finite-dimensional separation theorem.
  -- * Functional-analytic: construct a positive linear functional on a dense coordinate
  --   subalgebra of `C(MarkovParam k, ℝ)` consistent with `μ` and apply RMK.
  -- * Probabilistic: extend `μ` to a measure on infinite trajectories and use a martingale/tail
  --   σ-field construction of the random transition matrix.
  --
  -- The development currently contains all the scaffolding needed once this theorem is proved:
  -- continuous evidence polynomials, closed constraint sets, and the compactness reduction.
  intro u
  -- Reduce to the moment polytope membership statement.
  have hmem :
      MarkovDeFinettiHard.constraintVec (k := k) μ u ∈
        MarkovDeFinettiHard.momentPolytope (k := k) μ u := by
    exact MarkovDeFinettiHard.constraintVec_mem_momentPolytope
      (k := k) μ hμ hrec hcoreAll u
  -- Unpack membership as existence of a witness measure.
  rcases (MarkovDeFinettiHard.constraintVec_mem_momentPolytope_iff (k := k) μ u).1 hmem
    with ⟨π, hπ⟩
  exact (MarkovDeFinettiHard.finite_constraints_nonempty_iff (k := k) μ u).2 ⟨π, hπ⟩


theorem finite_constraints_nonempty_of_residualRate
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hrateAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧ HasExcursionResidualBoundRate (k := k) hk n e C) :
    ∀ u : Finset (ℕ × MarkovState k),
      (⋂ p ∈ u, MarkovDeFinettiHard.constraintSet (k := k) μ p.1 p.2).Nonempty := by
  intro u
  have hmem :
      MarkovDeFinettiHard.constraintVec (k := k) μ u ∈
        MarkovDeFinettiHard.momentPolytope (k := k) μ u := by
    exact MarkovDeFinettiHard.constraintVec_mem_momentPolytope_of_residualRate
      (k := k) μ hμ hrec hrateAll u
  rcases (MarkovDeFinettiHard.constraintVec_mem_momentPolytope_iff (k := k) μ u).1 hmem
    with ⟨π, hπ⟩
  exact (MarkovDeFinettiHard.finite_constraints_nonempty_iff (k := k) μ u).2 ⟨π, hπ⟩



theorem finite_constraints_nonempty_of_splitRates
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hsplitAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cw Cpc : ℝ,
        0 ≤ Cw ∧ 0 ≤ Cpc ∧
        HasCanonicalWRSmoothingRate (k := k) hk n e Cw ∧
        HasCanonicalWORTransportRate (k := k) hk n e Cw Cpc) :
    ∀ u : Finset (ℕ × MarkovState k),
      (⋂ p ∈ u, MarkovDeFinettiHard.constraintSet (k := k) μ p.1 p.2).Nonempty := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_splitRatesAll
      (k := k) hsplitAll
  exact finite_constraints_nonempty_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll



theorem finite_constraints_nonempty_of_exactSurrogateWORTransport
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hWORAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ Cpc : ℝ, 0 ≤ Cpc ∧
        HasCanonicalWORTransportRate (k := k) hk n e 0 Cpc) :
    ∀ u : Finset (ℕ × MarkovState k),
      (⋂ p ∈ u, MarkovDeFinettiHard.constraintSet (k := k) μ p.1 p.2).Nonempty := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_exactSurrogateWORTransportAll
      (k := k) hWORAll
  exact finite_constraints_nonempty_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll


theorem finite_constraints_nonempty_of_biapproxCore_exactSurrogate
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ u : Finset (ℕ × MarkovState k),
      (⋂ p ∈ u, MarkovDeFinettiHard.constraintSet (k := k) μ p.1 p.2).Nonempty := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll_exactSurrogate
      (k := k) hcoreAll
  exact finite_constraints_nonempty_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll

theorem finite_constraints_nonempty_of_explicitPatternSurrogateRate
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hpatternAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      ∃ C : ℝ, 0 ≤ C ∧
        HasPatternSurrogateResidualAlignmentRate (k := k) hk n e C) :
    ∀ u : Finset (ℕ × MarkovState k),
      (⋂ p ∈ u, MarkovDeFinettiHard.constraintSet (k := k) μ p.1 p.2).Nonempty := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_explicitPatternSurrogateRateAll
      (k := k) hpatternAll
  exact finite_constraints_nonempty_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll

theorem finite_constraints_nonempty_via_residualRateBridge
    (μ : FiniteAlphabet.PrefixMeasure (Fin k))
    (hμ : MarkovExchangeablePrefixMeasure (k := k) μ)
    (hrec : MarkovRecurrentPrefixMeasure (k := k) μ)
    (hcoreAll : ∀ hk : 0 < k, ∀ n : ℕ, ∀ e : MarkovState k,
      HasExcursionBiapproxCore (k := k) hk n e) :
    ∀ u : Finset (ℕ × MarkovState k),
      (⋂ p ∈ u, MarkovDeFinettiHard.constraintSet (k := k) μ p.1 p.2).Nonempty := by
  have hrateAll :=
    hasExcursionResidualBoundRateAll_of_biapproxCoreAll
      (k := k) hcoreAll
  exact finite_constraints_nonempty_of_residualRate
    (k := k) (μ := μ) hμ hrec hrateAll

end MarkovDeFinettiHard

end Mettapedia.Logic
