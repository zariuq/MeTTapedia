import Mettapedia.ProbabilityTheory.Distributions.BetaBernoulli
import Mettapedia.PLN.Evidence.EvidenceCounts

/-!
# Expected successes over a horizon of predictive draws

Under a Beta prior, the next `H` observations are drawn one at a time from the predictive, and
the prior is updated after each. The expected number of successes among them is `H` times the
current predictive probability `α / (α + β)` (`expectedSuccesses_eq`): averaged over the next
draw, the posterior mean is the prior mean (`mean_preserved`), so every future draw has the same
marginal probability of success.

For the uniform prior Beta(1, 1) after `n⁺` successes and `n⁻` failures the predictive is the
Laplace readout of the evidence counts, `uniformPosteriorMean n⁺ n⁻ = (n⁺ + 1) / (n⁺ + n⁻ + 2)`
(`laplace_mean`), and the expected number of successes among the next `H` is `H` times it
(`laplace_expectedSuccesses`).

A decision that weighs an expected gain per success against a fixed cost compares
`H (n⁺ + 1) g` with `c (n⁺ + n⁻ + 2)`: exact integer arithmetic over the common denominator
(`gain_exceeds_cost_iff`).
-/

namespace Mettapedia.ProbabilityTheory
namespace BetaBernoulliPrior

open Mettapedia.PLN.Evidence.EvidenceCounts

/-- The expected number of successes among `H` draws from the predictive, the prior updated
after each draw. -/
noncomputable def expectedSuccesses : ℕ → BetaBernoulliPrior → ℝ
  | 0, _ => 0
  | H + 1, prior =>
      prior.mean * (1 + expectedSuccesses H (prior.posterior true)) +
        (1 - prior.mean) * expectedSuccesses H (prior.posterior false)

/-- Averaged over the next draw from the predictive, the posterior mean is the prior mean. -/
theorem mean_preserved (prior : BetaBernoulliPrior) :
    prior.mean * (prior.posterior true).mean + (1 - prior.mean) * (prior.posterior false).mean =
      prior.mean := by
  have ha := prior.α_pos
  have hb := prior.β_pos
  have hab : prior.α + prior.β ≠ 0 := by linarith
  have hab1 : prior.α + 1 + prior.β ≠ 0 := by linarith
  have hab2 : prior.α + (prior.β + 1) ≠ 0 := by linarith
  simp only [mean, posterior, if_true, Bool.false_eq_true, if_false]
  field_simp
  ring

/-- Every future draw has the predictive's probability of success: the expected number of
successes among the next `H` is `H` times the predictive. -/
theorem expectedSuccesses_eq (H : ℕ) (prior : BetaBernoulliPrior) :
    expectedSuccesses H prior = H * prior.mean := by
  induction H generalizing prior with
  | zero => simp [expectedSuccesses]
  | succ H ih =>
    simp only [expectedSuccesses, ih]
    have h := mean_preserved prior
    push_cast
    linear_combination (H : ℝ) * h

/-- The uniform prior Beta(1, 1) after `npos` successes and `nneg` failures. -/
noncomputable def laplace (npos nneg : ℕ) : BetaBernoulliPrior where
  α := (npos : ℝ) + 1
  β := (nneg : ℝ) + 1
  α_pos := by positivity
  β_pos := by positivity

/-- Its predictive is the Laplace readout of the evidence counts. -/
theorem laplace_mean (npos nneg : ℕ) : (laplace npos nneg).mean = uniformPosteriorMean npos nneg := by
  simp only [mean, laplace, uniformPosteriorMean]
  congr 1
  ring

theorem laplace_expectedSuccesses (H npos nneg : ℕ) :
    expectedSuccesses H (laplace npos nneg) = H * uniformPosteriorMean npos nneg := by
  rw [expectedSuccesses_eq, laplace_mean]

/-- The decision rule, exactly: an expected gain `g` per success over the next `H` draws exceeds a
cost `c` exactly when `H (n⁺ + 1) g > c (n⁺ + n⁻ + 2)`, which is integer arithmetic. -/
theorem gain_exceeds_cost_iff (H npos nneg : ℕ) (g c : ℝ) :
    c < expectedSuccesses H (laplace npos nneg) * g ↔
      c * ((npos : ℝ) + nneg + 2) < (H : ℝ) * ((npos : ℝ) + 1) * g := by
  rw [laplace_expectedSuccesses, uniformPosteriorMean]
  have hd : (0 : ℝ) < (npos : ℝ) + nneg + 2 := by positivity
  constructor
  · intro h
    have := mul_lt_mul_of_pos_right h hd
    calc c * ((npos : ℝ) + nneg + 2)
        < (H : ℝ) * (((npos : ℝ) + 1) / ((npos : ℝ) + nneg + 2)) * g * ((npos : ℝ) + nneg + 2) := this
      _ = (H : ℝ) * ((npos : ℝ) + 1) * g := by field_simp
  · intro h
    have key : (H : ℝ) * (((npos : ℝ) + 1) / ((npos : ℝ) + nneg + 2)) * g =
        ((H : ℝ) * ((npos : ℝ) + 1) * g) / ((npos : ℝ) + nneg + 2) := by field_simp
    rw [key, lt_div_iff₀ hd]
    exact h

/-! ## Any Beta prior

A prior measured on another body of evidence is a Beta(α, β) with any positive `α`, `β`: after
`n⁺` successes and `n⁻` failures the predictive is `(α + n⁺) / (α + β + n⁺ + n⁻)`, and the
decision compares `H (α + n⁺) g` with `c (α + β + n⁺ + n⁻)`. -/

/-- The prior updated by `npos` successes and `nneg` failures. -/
noncomputable def afterCounts (prior : BetaBernoulliPrior) (npos nneg : ℕ) : BetaBernoulliPrior where
  α := prior.α + npos
  β := prior.β + nneg
  α_pos := by have := prior.α_pos; positivity
  β_pos := by have := prior.β_pos; positivity

theorem afterCounts_mean (prior : BetaBernoulliPrior) (npos nneg : ℕ) :
    (prior.afterCounts npos nneg).mean = (prior.α + npos) / (prior.α + prior.β + npos + nneg) := by
  simp only [mean, afterCounts]
  congr 1
  ring

theorem gain_exceeds_cost_iff_after (prior : BetaBernoulliPrior) (H npos nneg : ℕ) (g c : ℝ) :
    c < expectedSuccesses H (prior.afterCounts npos nneg) * g ↔
      c * (prior.α + prior.β + npos + nneg) < (H : ℝ) * (prior.α + npos) * g := by
  have hd : (0 : ℝ) < prior.α + prior.β + npos + nneg := by
    have := prior.α_pos; have := prior.β_pos; positivity
  have key : (H : ℝ) * ((prior.α + npos) / (prior.α + prior.β + npos + nneg)) * g =
      ((H : ℝ) * (prior.α + npos) * g) / (prior.α + prior.β + npos + nneg) := by
    field_simp
  rw [expectedSuccesses_eq, afterCounts_mean, key, lt_div_iff₀ hd]

/-! ## The probability of a sequence of observations

Drawing each observation from the predictive and updating after it, a sequence with `k` successes
and `m` failures has probability `α⁽ᵏ⁾ β⁽ᵐ⁾ / (α + β)⁽ᵏ⁺ᵐ⁾` (rising factorials,
`seqProb_eq`): it depends on the counts only, so on no order (`seqProb_perm`).  This is the
marginal likelihood of the evidence under the prior.

Two bodies of evidence (say, proofs from two libraries) share one rate or have one each: the
Bayes factor for sharing is the probability of all the observations as one sequence over the
product of the two sequences' probabilities (`poolingFactor`, `poolingFactor_eq`).  Adding the
counts of two bodies is exact only where they share a rate; this factor weighs the evidence that
they do. -/

/-- The probability of a sequence of observations, each drawn from the predictive, the prior
updated after it. -/
noncomputable def seqProb : BetaBernoulliPrior → List Bool → ℝ
  | _, [] => 1
  | prior, b :: bs => (if b then prior.mean else 1 - prior.mean) * seqProb (prior.posterior b) bs

/-- The rising factorial `x (x + 1) ⋯ (x + n - 1)`. -/
noncomputable def rising (x : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (x + i)

theorem rising_succ (x : ℝ) (n : ℕ) : rising x (n + 1) = x * rising (x + 1) n := by
  unfold rising
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring

theorem rising_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 < rising x n :=
  Finset.prod_pos fun i _ => by positivity

theorem seqProb_eq (prior : BetaBernoulliPrior) (l : List Bool) :
    seqProb prior l =
      rising prior.α (l.count true) * rising prior.β (l.count false) /
        rising (prior.α + prior.β) l.length := by
  induction l generalizing prior with
  | nil => simp [seqProb, rising]
  | cons b l ih =>
    have ha := prior.α_pos
    have hb := prior.β_pos
    have hab : 0 < prior.α + prior.β := by linarith
    cases b with
    | true =>
      have hpost := ih (prior.posterior true)
      simp only [posterior, if_true] at hpost
      have hsum : prior.α + 1 + prior.β = prior.α + prior.β + 1 := by ring
      rw [hsum] at hpost
      have hr := rising_pos (show 0 < prior.α + prior.β + 1 by linarith) l.length
      simp only [seqProb, if_true, hpost, posterior, mean, List.count_cons_self, List.length_cons,
        List.count_cons, rising_succ prior.α, rising_succ (prior.α + prior.β)]
      simp
      field_simp
    | false =>
      have hpost := ih (prior.posterior false)
      simp only [posterior, Bool.false_eq_true, if_false] at hpost
      have hsum : prior.α + (prior.β + 1) = prior.α + prior.β + 1 := by ring
      rw [hsum] at hpost
      have hr := rising_pos (show 0 < prior.α + prior.β + 1 by linarith) l.length
      have hct : (false :: l).count true = l.count true := by simp
      have hcf : (false :: l).count false = l.count false + 1 := by simp
      rw [hct, hcf, List.length_cons, rising_succ prior.β, rising_succ (prior.α + prior.β)]
      simp only [seqProb, Bool.false_eq_true, if_false, hpost, posterior, mean]
      field_simp
      ring

theorem seqProb_perm (prior : BetaBernoulliPrior) {l₁ l₂ : List Bool} (h : l₁.Perm l₂) :
    seqProb prior l₁ = seqProb prior l₂ := by
  rw [seqProb_eq, seqProb_eq, h.count_eq, h.count_eq, h.length_eq]

/-- The Bayes factor for one shared rate against one rate for each of two bodies of evidence,
under the same prior. -/
noncomputable def poolingFactor (prior : BetaBernoulliPrior) (l₁ l₂ : List Bool) : ℝ :=
  seqProb prior (l₁ ++ l₂) / (seqProb prior l₁ * seqProb prior l₂)

theorem poolingFactor_eq (prior : BetaBernoulliPrior) (l₁ l₂ : List Bool) :
    poolingFactor prior l₁ l₂ =
      (rising prior.α (l₁.count true + l₂.count true) * rising prior.β (l₁.count false + l₂.count false) /
          rising (prior.α + prior.β) (l₁.length + l₂.length)) /
        ((rising prior.α (l₁.count true) * rising prior.β (l₁.count false) /
            rising (prior.α + prior.β) l₁.length) *
          (rising prior.α (l₂.count true) * rising prior.β (l₂.count false) /
            rising (prior.α + prior.β) l₂.length)) := by
  simp only [poolingFactor, seqProb_eq, List.count_append, List.length_append]

/-! ## Examples -/

/-- The uniform prior. -/
noncomputable def uniform : BetaBernoulliPrior := laplace 0 0

/-- Three successes and a failure in one body, four failures in the other: the factor is 25/126,
evidence that the two have different rates. -/
example : poolingFactor uniform [true, true, true, false] [false, false, false, false] = 25 / 126 := by
  rw [poolingFactor_eq]
  simp [uniform, laplace, rising, Finset.prod_range_succ]
  norm_num

/-- Two successes and two failures in each: the factor is 10/7, evidence for one shared rate. -/
example : poolingFactor uniform [true, true, false, false] [true, false, true, false] = 10 / 7 := by
  rw [poolingFactor_eq]
  simp [uniform, laplace, rising, Finset.prod_range_succ]
  norm_num

/-- The order of the evidence does not matter. -/
example : seqProb uniform [true, false, false] = seqProb uniform [false, false, true] :=
  seqProb_perm uniform (by decide)

/-- No evidence: one success expected in two draws. -/
example : expectedSuccesses 2 (laplace 0 0) = 1 := by
  rw [laplace_expectedSuccesses, uniformPosteriorMean]
  norm_num

/-- One failure observed: three draws expect one success, not none. The plug-in rate `0 / 1`
would expect none: it is not the predictive. -/
example : expectedSuccesses 3 (laplace 0 1) = 1 ∧ expectedSuccesses 3 (laplace 0 1) ≠ 3 * (0 / 1 : ℝ) := by
  rw [laplace_expectedSuccesses, uniformPosteriorMean]
  norm_num

end BetaBernoulliPrior
end Mettapedia.ProbabilityTheory
