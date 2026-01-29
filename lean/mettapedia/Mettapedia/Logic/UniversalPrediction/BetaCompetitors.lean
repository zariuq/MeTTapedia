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

end BetaCompetitors

end Mettapedia.Logic.UniversalPrediction
