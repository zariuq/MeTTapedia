import Mettapedia.Logic.UniversalPrediction.EnumerationBridge
import Mettapedia.Logic.UniversalPrediction.BetaPredictor

/-!
# Beta-family competitors for universal prediction (dominance/regret)

This file instantiates the abstract dominance→regret bound from
`UniversalPrediction/EnumerationBridge.lean` with three Beta-family predictors:

- Laplace/uniform: `Beta(1,1)`
- Jeffreys/KT: `Beta(1/2,1/2)`
- Haldane (improper limit): `α = β → 0` (implemented as a limit predictor)

We **do not** prove these predictors are computable here; instead we keep that as an
explicit hypothesis `E.IsComputable μ`, so the regret bounds “turn on” immediately
once an enumeration theorem is supplied.
-/

noncomputable section

namespace Mettapedia.Logic.UniversalPrediction

open scoped Classical
open FiniteHorizon

namespace BetaCompetitors

open EnumerationBridge

/-- Universal-mixture regret bound for the Laplace/uniform predictor, assuming it is in-scope. -/
theorem relEntropy_le_log_inv_laplace
    (E : PrefixMeasureEnumeration)
    (hμ : E.IsComputable laplacePrefixMeasure)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (E.xi) laplacePrefixMeasure c ∧
      relEntropy laplacePrefixMeasure (E.xi) n ≤ Real.log (1 / c.toReal) := by
  simpa using
    (PrefixMeasureEnumeration.relEntropy_le_log_inv_of_IsComputable
      (E := E) (μ := laplacePrefixMeasure) hμ n)

/-- Universal-mixture regret bound for the Jeffreys/KT predictor, assuming it is in-scope. -/
theorem relEntropy_le_log_inv_jeffreys
    (E : PrefixMeasureEnumeration)
    (hμ : E.IsComputable jeffreysPrefixMeasure)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (E.xi) jeffreysPrefixMeasure c ∧
      relEntropy jeffreysPrefixMeasure (E.xi) n ≤ Real.log (1 / c.toReal) := by
  simpa using
    (PrefixMeasureEnumeration.relEntropy_le_log_inv_of_IsComputable
      (E := E) (μ := jeffreysPrefixMeasure) hμ n)

/-- Universal-mixture regret bound for the Haldane limit predictor, assuming it is in-scope. -/
theorem relEntropy_le_log_inv_haldane
    (E : PrefixMeasureEnumeration)
    (hμ : E.IsComputable haldanePrefixMeasure)
    (n : ℕ) :
    ∃ c : ENNReal, c ≠ 0 ∧ Dominates (E.xi) haldanePrefixMeasure c ∧
      relEntropy haldanePrefixMeasure (E.xi) n ≤ Real.log (1 / c.toReal) := by
  simpa using
    (PrefixMeasureEnumeration.relEntropy_le_log_inv_of_IsComputable
      (E := E) (μ := haldanePrefixMeasure) hμ n)

/-! ## Chain Composition: PLN → ξ → μ

The νPLN paper investigates whether PLN's regret relative to the true environment μ
is bounded by K(PLN) + K(μ). This section formalizes what we can prove.

**What we have:**
- `D(μ || ξ) ≤ log(1/c_μ)` — ξ predicts μ well, from a dominance constant `c_μ`
- `ξ` dominates PLN with some `c_PLN > 0` once PLN is in the enumeration

**The gap:** These don't directly compose to give `D(μ || PLN)`.
- `D(μ || ξ)` measures ξ's loss on μ-data
- `D(PLN || ξ)` measures ξ's loss on PLN-data (not PLN's loss on anything)

**What IS proven:**
- Both μ and PLN are dominated by ξ (they're in the mixture)
- ξ has bounded regret relative to μ
- For 0-1 loss, `average_regret_vanishes` shows ξ's average error → 0
-/

/-- **The proven chain components.**

We can prove both pieces of the chain separately:
1. D(μ || ξ) ≤ log(1/c_μ) from dominance `Dominates ξ μ c_μ`
2. ξ dominates PLN once PLN is in the enumeration (giving some `c_PLN > 0`)

The composition to get D(μ || PLN) requires additional structure. -/
theorem nupln_chain_components
    (E : PrefixMeasureEnumeration)
    (μ : PrefixMeasure) (hμ : E.IsComputable μ)
    (hPLN : E.IsComputable haldanePrefixMeasure)
    (n : ℕ) :
    -- Component 1: ξ predicts μ well (D(μ || ξ) bounded)
    (∃ c_μ : ENNReal, c_μ ≠ 0 ∧
      Dominates (E.xi) μ c_μ ∧
      relEntropy μ (E.xi) n ≤ Real.log (1 / c_μ.toReal)) ∧
    -- Component 2: ξ dominates PLN
    (∃ c_PLN : ENNReal, c_PLN ≠ 0 ∧
      Dominates (E.xi) haldanePrefixMeasure c_PLN) := by
  refine ⟨?_, ?_⟩
  -- Component 1: μ → ξ bound
  · obtain ⟨c_μ, hc0, hdom, hbound⟩ := E.relEntropy_le_log_inv_of_IsComputable μ hμ n
    exact ⟨c_μ, hc0, hdom, hbound⟩
  -- Component 2: ξ dominates PLN
  · obtain ⟨c_PLN, hdom, hc0⟩ := E.exists_dominance_of_IsComputable haldanePrefixMeasure hPLN
    exact ⟨encodeWeight c_PLN, E.encodeWeight_ne_zero c_PLN, hdom⟩

end BetaCompetitors

end Mettapedia.Logic.UniversalPrediction
