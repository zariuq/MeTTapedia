import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

/-!
# PLN revision as an implicit natural-gradient step

Meredith's graded where-clause paper (*Graded Where-Clauses over the Reals*,
F1R3FLY fuzzyware, 2026) derives PLN from the requirement that gradient
descent on a grade fibre be taken correctly: the naive step on a strength
does not know how much evidence stands behind the value, the correcting
metric is the Fisher information, the Fisher information of a Bernoulli
parameter is an evidence count, and a strength together with a count is a
PLN simple truth value.  Its headline (his Theorem `natgrad`): PLN revision
is the natural-gradient ascent step on the Bernoulli log-likelihood with
unit step size and the Fisher metric evaluated at the POSTERIOR count — and
because the metric is evaluated after the increment, the step is the
implicit (proximal) discretisation, hence unconditionally stable.

The paper proves this on paper and validates it numerically (discrepancy
1.1e-16 with the metric at the posterior count, 4.6e-1 at the prior count).
This module makes the identity, its sharp negative control, the stability
corollary, and the inflation-rigidity proposition kernel-checked.

Statements are over ℝ in the (strength, count) chart, matching the paper.
The score of a Bernoulli observation x at strength s is
(x − s)/(s(1−s)); the Fisher information at count n is n/(s(1−s)).
-/

namespace Mettapedia.PLN.Bridges.GSLT.RevisionNaturalGradient

/-- Bernoulli score (∂/∂s of the log-likelihood of observation `x`). -/
noncomputable def score (s x : ℝ) : ℝ := (x - s) / (s * (1 - s))

/-- Fisher information of the Bernoulli parameter at evidence count `n`. -/
noncomputable def fisher (s n : ℝ) : ℝ := n / (s * (1 - s))

/-- The strength component of PLN revision by one observation of value `x`. -/
noncomputable def revisedStrength (s n x : ℝ) : ℝ := (n * s + x) / (n + 1)

/-- Revision moves the strength by exactly `(x − s)/(n + 1)`. -/
theorem revisedStrength_sub {s x : ℝ} (n : ℝ) (hn1 : n + 1 ≠ 0) :
    revisedStrength s n x - s = (x - s) / (n + 1) := by
  unfold revisedStrength
  field_simp
  ring

/-- The natural-gradient step at count `m` moves the strength by
`(x − s)/m`: the Fisher factors cancel the score's variance factor. -/
theorem natgrad_step_eq {s m x : ℝ}
    (hs : s ≠ 0) (h1s : (1 : ℝ) - s ≠ 0) (hm : m ≠ 0) :
    (fisher s m)⁻¹ * score s x = (x - s) / m := by
  unfold fisher score
  field_simp

/-- **The headline identity** (Meredith, Theorem natgrad): revision equals
the natural-gradient step with unit step size and the Fisher metric
evaluated at the POSTERIOR count `n + 1`. -/
theorem revision_is_natural_gradient_step
    {s n : ℝ} (x : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) (hn : 0 < n) :
    revisedStrength s n x = s + (fisher s (n + 1))⁻¹ * score s x := by
  have hn1 : n + 1 ≠ 0 := by positivity
  rw [natgrad_step_eq (ne_of_gt hs₀) (by linarith) hn1,
    ← revisedStrength_sub n hn1]
  ring

/-- **The negative control, proved rather than measured**: with the Fisher
metric at the PRIOR count the identity fails whenever the observation moves
the strength at all.  It is this step and not the neighbouring one. -/
theorem revision_ne_prior_count_step
    {s n x : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) (hn : 0 < n) (hmove : x ≠ s) :
    revisedStrength s n x ≠ s + (fisher s n)⁻¹ * score s x := by
  have hn1 : n + 1 ≠ 0 := by positivity
  rw [natgrad_step_eq (ne_of_gt hs₀) (by linarith) (ne_of_gt hn)]
  intro h
  have hsub : (x - s) / (n + 1) = (x - s) / n := by
    rw [← revisedStrength_sub n hn1, h]
    ring
  have hne : x - s ≠ 0 := sub_ne_zero.mpr hmove
  have := (div_eq_div_iff (by positivity) (ne_of_gt hn)).mp hsub
  apply hne
  nlinarith [this]

/-- **Implicit ⇒ stable** (Meredith, Corollary implicit): the revised
strength is a convex combination of `s` and `x`, so for an observation in
the unit interval the result stays strictly inside `(0,1)` — the step can
never be absorbed at an endpoint, where the score is undefined and the
hypothesis dies. -/
theorem revisedStrength_mem_open_unit
    {s n x : ℝ} (hs₀ : 0 < s) (hs₁ : s < 1) (hn : 0 < n)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) :
    0 < revisedStrength s n x ∧ revisedStrength s n x < 1 := by
  have hn1 : (0:ℝ) < n + 1 := by linarith
  unfold revisedStrength
  constructor
  · have hnum : 0 < n * s + x := by nlinarith
    exact div_pos hnum hn1
  · rw [div_lt_one hn1]
    nlinarith

/-- **Inflation collapses the step size** (Meredith, Proposition freeze):
scaling the evidence count by `λ > 1` strictly shrinks the distance a
single observation can move the strength.  A learner with counterfeit
confidence is not unstable; it is rigid. -/
theorem inflation_shrinks_step
    {s n x lam : ℝ} (hn : 0 < n) (hlam : 1 < lam) (hmove : x ≠ s) :
    |revisedStrength s (lam * n) x - s| < |revisedStrength s n x - s| := by
  have hn1 : (0:ℝ) < n + 1 := by linarith
  have hln1 : (0:ℝ) < lam * n + 1 := by nlinarith
  rw [revisedStrength_sub n (ne_of_gt hn1),
    revisedStrength_sub (lam * n) (ne_of_gt hln1), abs_div, abs_div,
    abs_of_pos hn1, abs_of_pos hln1]
  have hxs : 0 < |x - s| := abs_pos.mpr (sub_ne_zero.mpr hmove)
  apply div_lt_div_of_pos_left hxs hn1
  nlinarith

end Mettapedia.PLN.Bridges.GSLT.RevisionNaturalGradient
