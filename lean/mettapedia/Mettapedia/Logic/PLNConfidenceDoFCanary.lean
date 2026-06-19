import Mettapedia.Logic.WalleyBinaryIDM
import Mettapedia.Logic.EvidenceBeta
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

DoF 14 (completion-level extreme point) needs no new theorem: the strict-width
envelope of the two-spin magnet is already a property of the *credal set* (not of
any completion) — witnessed by `…ImpreciseProbability.ProjectiveCredal.nEnvelope_nontrivial`.
So the STV read-off, being a function of the envelope, is invariant to which
completion the world selects.
-/

namespace Mettapedia.Logic.PLNConfidenceDoFCanary

open Mettapedia.Logic.EvidenceBeta Mettapedia.Logic.WalleyBinaryIDM

/-- **DoF 8 — Backend for uncertainty (Bayesian Beta vs Walley IDM).**
On the SAME counts (2 positive, 3 negative): the Bayesian uniform-prior posterior
MEAN (a single point, `3/7`) lies strictly inside the Walley IDM predictive
INTERVAL `[2/7, 4/7]` (strength `s = 2`), which itself has strictly positive width.
A precise point estimate and a robust interval are genuinely different backends —
collapsing the interval to the point hides real imprecision. -/
theorem beta_mean_strictly_inside_walley_idm_interval :
    lowerEndpoint 2 3 2 < (withUniformPrior 2 3).posteriorMean ∧
      (withUniformPrior 2 3).posteriorMean < upperEndpoint 2 3 2 ∧
      lowerEndpoint 2 3 2 < upperEndpoint 2 3 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [lowerEndpoint, upperEndpoint, EvidenceBetaParams.posteriorMean,
      EvidenceBetaParams.alpha, EvidenceBetaParams.beta, withUniformPrior] <;>
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

/-- **DoF 18 — Provenance / route semantics.**
On the SAME counts `(3, 0)`, confidence depends on the route (`3/4` direct vs
`3/11` pathway), while strength does not depend on the route at all (it has no
`Route` argument). Same final `<s,c>`-strength, different provenance-aware
confidence. -/
theorem route_kappa_changes_confidence_not_strength :
    routeConf Route.direct 3 0 = 3 / 4 ∧
      routeConf Route.pathway 3 0 = 3 / 11 ∧
      routeConf Route.direct 3 0 ≠ routeConf Route.pathway 3 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [routeConf, routeKappa] <;> norm_num

/-- Aggregator: the three new degree-of-freedom canaries at sample points, for a
single `#print axioms` seal. -/
theorem fullDoFZooProfile :
    (lowerEndpoint 2 3 2 < (withUniformPrior 2 3).posteriorMean) ∧
      (Real.log ((2 : ℝ) ^ (2 : ℝ)) - Real.log ((3 : ℝ) ^ (2 : ℝ))
        = 2 * (Real.log 2 - Real.log 3)) ∧
      (routeConf Route.direct 3 0 ≠ routeConf Route.pathway 3 0) :=
  ⟨beta_mean_strictly_inside_walley_idm_interval.1,
    power_discount_scales_logodds 2 3 2 (by norm_num) (by norm_num),
    route_kappa_changes_confidence_not_strength.2.2⟩

end Mettapedia.Logic.PLNConfidenceDoFCanary
