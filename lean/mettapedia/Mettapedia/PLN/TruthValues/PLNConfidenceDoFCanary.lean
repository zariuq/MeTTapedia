import Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM
import Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# PLN confidence degrees-of-freedom canaries

Small, concrete theorems backing the runnable example pack
`Mettapedia/papers/pln-confidence-examples/`. Each is the Lean *oracle* for a
degree of freedom whose `.metta` demonstration is intuition only.

- **DoF 8 (backend)** `beta_mean_strictly_inside_walley_idm_interval`
- **DoF 11 (discounting)** `power_discount_scales_logodds`
- **DoF 18 (provenance/route)** `route_kappa_changes_confidence_not_strength`

DoF 14 (completion-level extreme point) needs no new theorem: the existing
bounded-measurable credal layer expresses completion disagreement with
`boundedMeasurableCredalSetHasStrictWidth`, and
`boundedMeasurableCredalSet_not_determines_of_strictWidth` proves that such
completion freedom prevents a determined single readout.
-/

namespace Mettapedia.PLN.TruthValues.PLNConfidenceDoFCanary

open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceBeta Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM

/-- **DoF 8 — Backend for uncertainty (Bayesian Beta vs Walley IDM).**
On the SAME counts (2 positive, 3 negative): the Bayesian uniform-prior posterior
MEAN (a single point, `3/7`) lies strictly inside the Walley IDM predictive
INTERVAL `[2/7, 4/7]` (strength `s = 2`), which itself has strictly positive width.
A precise point estimate and a robust interval are genuinely different backends —
collapsing the interval to the point hides real imprecision. -/
theorem beta_idm_sample_values :
    lowerEndpoint 2 3 2 = (2 / 7 : ℝ) ∧
      (withUniformPrior 2 3).posteriorMean = (3 / 7 : ℝ) ∧
      upperEndpoint 2 3 2 = (4 / 7 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lowerEndpoint, upperEndpoint, EvidenceBetaParams.posteriorMean,
      EvidenceBetaParams.alpha, EvidenceBetaParams.beta, withUniformPrior] <;>
    norm_num

theorem beta_mean_strictly_inside_walley_idm_interval :
    lowerEndpoint 2 3 2 < (withUniformPrior 2 3).posteriorMean ∧
      (withUniformPrior 2 3).posteriorMean < upperEndpoint 2 3 2 ∧
      lowerEndpoint 2 3 2 < upperEndpoint 2 3 2 := by
  rcases beta_idm_sample_values with ⟨hlo, hmid, hhi⟩
  rw [hlo, hmid, hhi]
  norm_num

/-- **DoF 11 — Feature/evidence discounting.**
The `evidence-power` regraduation raises both counts to a power `w`; this scales
the log-odds (the Bernoulli natural parameter `log p − log n`) by exactly `w`:
`w < 1` discounts (correlated/duplicate evidence), `w = 1` is unchanged,
`w > 1` amplifies (independent curated evidence), `w = 0` ignores the feature. -/
theorem power_discount_scales_logodds (p n w : ℝ) (hp : 0 < p) (hn : 0 < n) :
    Real.log (p ^ w) - Real.log (n ^ w) = w * (Real.log p - Real.log n) := by
  rw [Real.log_rpow hp, Real.log_rpow hn]; ring

/-- A route tag carrying a route-specific evidence scale `κ`. -/
inductive Route
  | direct
  | pathway

/-- Route-specific evidence scale: direct evidence is trusted (small κ),
pathway-mediated evidence is model-dependent (large κ). -/
def routeKappa : Route → ℝ
  | Route.direct => 1
  | Route.pathway => 8

/-- Strength does NOT take a `Route` argument — it is route-independent by
construction (the formal content of "provenance does not change strength"). -/
noncomputable def routeStrength (pos neg : ℝ) : ℝ := pos / (pos + neg)

/-- Confidence carries the route-specific scale. -/
noncomputable def routeConf (r : Route) (pos neg : ℝ) : ℝ :=
  (pos + neg) / (pos + neg + routeKappa r)

/-- The displayed route-aware truth readout: common strength plus
route-dependent confidence. -/
noncomputable def routeReadout (r : Route) (pos neg : ℝ) : ℝ × ℝ :=
  (routeStrength pos neg, routeConf r pos neg)

/-- **DoF 18 — Provenance / route semantics.**
On the SAME counts `(3, 0)`, confidence depends on the route (`3/4` direct vs
`3/11` pathway), while strength is the same first coordinate. Same displayed
strength, different provenance-aware confidence. -/
theorem route_kappa_changes_confidence_not_strength :
    (routeReadout Route.direct 3 0).1 =
        (routeReadout Route.pathway 3 0).1 ∧
      (routeReadout Route.direct 3 0).2 = 3 / 4 ∧
      (routeReadout Route.pathway 3 0).2 = 3 / 11 ∧
      (routeReadout Route.direct 3 0).2 ≠
        (routeReadout Route.pathway 3 0).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [routeReadout, routeStrength, routeConf, routeKappa] <;>
    norm_num

/-- Aggregator: the three new degree-of-freedom canaries at sample points, for a
single `#print axioms` seal. -/
theorem fullDoFZooProfile :
    (lowerEndpoint 2 3 2 < (withUniformPrior 2 3).posteriorMean ∧
      (withUniformPrior 2 3).posteriorMean < upperEndpoint 2 3 2 ∧
      lowerEndpoint 2 3 2 < upperEndpoint 2 3 2) ∧
      (∀ p n w : ℝ, 0 < p → 0 < n →
        Real.log (p ^ w) - Real.log (n ^ w) =
          w * (Real.log p - Real.log n)) ∧
      ((routeReadout Route.direct 3 0).1 =
          (routeReadout Route.pathway 3 0).1 ∧
        (routeReadout Route.direct 3 0).2 = 3 / 4 ∧
        (routeReadout Route.pathway 3 0).2 = 3 / 11 ∧
        (routeReadout Route.direct 3 0).2 ≠
          (routeReadout Route.pathway 3 0).2) :=
  ⟨beta_mean_strictly_inside_walley_idm_interval,
    fun p n w hp hn => power_discount_scales_logodds p n w hp hn,
    route_kappa_changes_confidence_not_strength⟩

end Mettapedia.PLN.TruthValues.PLNConfidenceDoFCanary
