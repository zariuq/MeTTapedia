import Mathlib.Analysis.Convex.Strong

/-!
# Partial strong convexity implies a Polyak--Łojasiewicz bound

Some learning objectives are strongly convex only in a distinguished block of
parameters.  If minimizing that block reaches the same global value for every
admissible nuisance parameter, the norm of the partial gradient still controls
the full objective gap.

This file proves that implication on a real Hilbert space.  A domination lemma
then lifts the partial-gradient estimate to any larger recorded gradient norm.
The scalar coupled-valley fixture is partially strongly convex but has a flat
family of global minima, so it is not strongly convex on the product space.
A shifted-valley fixture shows that a nuisance-dependent restricted minimum
breaks the PL conclusion.

Source correspondence: Liao and Kyrillidis, *Provable Accelerated Convergence
of Nesterov's Momentum for Deep ReLU Neural Networks*, arXiv:2306.08109,
Assumptions 1 and 6 and Lemma 4.  The Hilbert-space certificate and the two
separation fixtures are generalizations used here to expose the exact
hypothesis boundary.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace PartialStrongConvexityPL

open Set
open scoped InnerProductSpace

variable {Primary Nuisance : Type*}
  [NormedAddCommGroup Primary] [InnerProductSpace ℝ Primary]

/-- Partial strong convexity together with a nuisance-independent restricted
minimum.  The declared partial gradient is checked by the lower-model
inequality rather than trusted as a derivative by name. -/
structure Certificate
    (objective : Primary → Nuisance → ℝ)
    (partialGradient : Primary → Nuisance → Primary)
    (minimum modulus : ℝ) where
  modulus_pos : 0 < modulus
  minimizer : Nuisance → Primary
  minimum_value : ∀ nuisance,
    objective (minimizer nuisance) nuisance = minimum
  lower : ∀ primary nuisance,
    modulus / 2 * ‖minimizer nuisance - primary‖ ^ 2 ≤
      objective (minimizer nuisance) nuisance -
        (objective primary nuisance +
          ⟪partialGradient primary nuisance,
            minimizer nuisance - primary⟫_ℝ)

/-- Partial strong convexity and a shared restricted minimum imply the
Polyak--Łojasiewicz inequality for the partial gradient. -/
theorem partialGradient_sq_ge_twice_gap
    {objective : Primary → Nuisance → ℝ}
    {partialGradient : Primary → Nuisance → Primary}
    {minimum modulus : ℝ}
    (certificate :
      Certificate objective partialGradient minimum modulus)
    (primary : Primary) (nuisance : Nuisance) :
    2 * modulus * (objective primary nuisance - minimum) ≤
      ‖partialGradient primary nuisance‖ ^ 2 := by
  let difference := certificate.minimizer nuisance - primary
  let gradient := partialGradient primary nuisance
  have lower := certificate.lower primary nuisance
  rw [certificate.minimum_value nuisance] at lower
  have cauchy :
      -⟪gradient, difference⟫_ℝ ≤ ‖gradient‖ * ‖difference‖ := by
    have := real_inner_le_norm (-gradient) difference
    simpa [gradient, difference] using this
  have square_nonneg :
      0 ≤ (‖gradient‖ - modulus * ‖difference‖) ^ 2 :=
    sq_nonneg _
  have modulus_pos := certificate.modulus_pos
  dsimp [gradient, difference] at cauchy square_nonneg ⊢
  nlinarith

/-- Any recorded full-gradient norm that dominates the partial-gradient norm
inherits the same PL lower bound. -/
theorem fullGradient_sq_ge_twice_gap
    {FullGradient : Type*} [NormedAddCommGroup FullGradient]
    {objective : Primary → Nuisance → ℝ}
    {partialGradient : Primary → Nuisance → Primary}
    {fullGradient : Primary → Nuisance → FullGradient}
    {minimum modulus : ℝ}
    (certificate :
      Certificate objective partialGradient minimum modulus)
    (norm_dominates : ∀ primary nuisance,
      ‖partialGradient primary nuisance‖ ≤
        ‖fullGradient primary nuisance‖)
    (primary : Primary) (nuisance : Nuisance) :
    2 * modulus * (objective primary nuisance - minimum) ≤
      ‖fullGradient primary nuisance‖ ^ 2 := by
  have partialPL :=
    partialGradient_sq_ge_twice_gap certificate primary nuisance
  have partial_norm_nonneg :
      0 ≤ ‖partialGradient primary nuisance‖ := norm_nonneg _
  have full_norm_nonneg : 0 ≤ ‖fullGradient primary nuisance‖ := norm_nonneg _
  have normSq :
      ‖partialGradient primary nuisance‖ ^ 2 ≤
        ‖fullGradient primary nuisance‖ ^ 2 := by
    nlinarith [norm_dominates primary nuisance]
  exact partialPL.trans normSq

/-! ## Nuisance-drift budget -/

/-- A smooth loss and a Lipschitz nuisance channel turn nuisance motion into
one objective-gap term and one quadratic motion term.

The hypotheses are stated as observable scalar inequalities so the result can
be instantiated by an analytic model, an exact replay certificate, or a
runtime trace without trusting the names of its fields. -/
theorem nuisanceDrift_le_gap_add_quadratic
    {lossSmoothness channelLipschitz tradeoff objectiveGap
      nuisanceDistance gradientNorm modelDrift objectiveDrift : ℝ}
    (lossSmoothness_nonneg : 0 ≤ lossSmoothness)
    (tradeoff_pos : 0 < tradeoff)
    (modelDrift_nonneg : 0 ≤ modelDrift)
    (gradient_gap :
      gradientNorm ^ 2 ≤ 2 * lossSmoothness * objectiveGap)
    (channel_bound :
      modelDrift ≤ channelLipschitz * nuisanceDistance)
    (smooth_upper :
      objectiveDrift ≤
        gradientNorm * modelDrift +
          lossSmoothness / 2 * modelDrift ^ 2) :
    objectiveDrift ≤
      lossSmoothness / tradeoff * objectiveGap +
        channelLipschitz ^ 2 / 2 *
          (lossSmoothness + tradeoff) * nuisanceDistance ^ 2 := by
  have tradeoff_nonneg : 0 ≤ tradeoff := le_of_lt tradeoff_pos
  have denominator_pos : 0 < 2 * tradeoff := mul_pos (by norm_num) tradeoff_pos
  have young :
      gradientNorm * modelDrift ≤
        gradientNorm ^ 2 / (2 * tradeoff) +
          tradeoff / 2 * modelDrift ^ 2 := by
    have balanced :
        2 * gradientNorm * modelDrift ≤
          tradeoff⁻¹ * gradientNorm ^ 2 +
            tradeoff * modelDrift ^ 2 := by
      simpa using
        (two_mul_le_add_mul_sq
          (a := gradientNorm) (b := modelDrift)
          (inv_pos.mpr tradeoff_pos))
    calc
      gradientNorm * modelDrift ≤
          (tradeoff⁻¹ * gradientNorm ^ 2 +
            tradeoff * modelDrift ^ 2) / 2 := by
        nlinarith
      _ =
          gradientNorm ^ 2 / (2 * tradeoff) +
            tradeoff / 2 * modelDrift ^ 2 := by
        field_simp [ne_of_gt tradeoff_pos]
  have gradientTerm :
      gradientNorm ^ 2 / (2 * tradeoff) ≤
        lossSmoothness / tradeoff * objectiveGap := by
    apply (div_le_iff₀ denominator_pos).2
    field_simp
    nlinarith
  have channelSq :
      modelDrift ^ 2 ≤
        channelLipschitz ^ 2 * nuisanceDistance ^ 2 := by
    nlinarith
  have combinedCoefficient_nonneg :
      0 ≤ (lossSmoothness + tradeoff) / 2 := by positivity
  calc
    objectiveDrift ≤
        gradientNorm * modelDrift +
          lossSmoothness / 2 * modelDrift ^ 2 := smooth_upper
    _ ≤
        gradientNorm ^ 2 / (2 * tradeoff) +
          (lossSmoothness + tradeoff) / 2 * modelDrift ^ 2 := by
      calc
        gradientNorm * modelDrift +
            lossSmoothness / 2 * modelDrift ^ 2 ≤
            (gradientNorm ^ 2 / (2 * tradeoff) +
              tradeoff / 2 * modelDrift ^ 2) +
              lossSmoothness / 2 * modelDrift ^ 2 := by
          gcongr
        _ =
            gradientNorm ^ 2 / (2 * tradeoff) +
              (lossSmoothness + tradeoff) / 2 * modelDrift ^ 2 := by ring
    _ ≤
        lossSmoothness / tradeoff * objectiveGap +
          (lossSmoothness + tradeoff) / 2 *
            (channelLipschitz ^ 2 * nuisanceDistance ^ 2) := by
      exact add_le_add gradientTerm
        (mul_le_mul_of_nonneg_left channelSq combinedCoefficient_nonneg)
    _ =
        lossSmoothness / tradeoff * objectiveGap +
          channelLipschitz ^ 2 / 2 *
            (lossSmoothness + tradeoff) * nuisanceDistance ^ 2 := by ring

/-- Without the gradient-to-gap inequality, the source nuisance-drift budget
can fail even when every scalar is finite and nonnegative. -/
theorem gradientGapBound_is_loadBearing :
    ¬ (1 : ℝ) ≤
      0 / 1 * 0 + 1 ^ 2 / 2 * (0 + 1) * 1 ^ 2 := by
  norm_num

/-! ## Scalar recovery and separation fixtures -/

/-- A valley with a nuisance-indexed minimizer but a shared minimum value. -/
noncomputable def coupledValley (primary nuisance : ℝ) : ℝ :=
  (primary - nuisance) ^ 2 / 2

noncomputable def coupledValleyPartialGradient
    (primary nuisance : ℝ) : ℝ :=
  primary - nuisance

/-- The coupled valley has an exact unit partial-strong-convexity
certificate. -/
noncomputable def coupledValleyCertificate :
    Certificate coupledValley coupledValleyPartialGradient 0 1 where
  modulus_pos := by norm_num
  minimizer := id
  minimum_value := by
    intro nuisance
    simp [coupledValley]
  lower := by
    intro primary nuisance
    simp only [coupledValley, coupledValleyPartialGradient, id_eq,
      Real.inner_apply]
    rw [Real.norm_eq_abs, sq_abs]
    ring_nf
    exact le_rfl

/-- On the coupled valley the partial PL inequality is attained exactly. -/
theorem coupledValley_partialPL_exact (primary nuisance : ℝ) :
    2 * 1 * (coupledValley primary nuisance - 0) =
      ‖coupledValleyPartialGradient primary nuisance‖ ^ 2 := by
  rw [Real.norm_eq_abs, sq_abs]
  simp only [coupledValley, coupledValleyPartialGradient, sub_zero, mul_one]
  ring

/-- Partial strong convexity is strictly weaker than strong convexity on the
whole product: the coupled valley is flat along the diagonal. -/
theorem coupledValley_not_strongConvexOn_product
    (modulus : ℝ) (modulus_pos : 0 < modulus) :
    ¬ StrongConvexOn (Set.univ : Set (ℝ × ℝ)) modulus
      (fun state => coupledValley state.1 state.2) := by
  intro claimed
  have strict := claimed.strictConvexOn modulus_pos
  have midpoint := strict.2
    (Set.mem_univ ((0, 0) : ℝ × ℝ))
    (Set.mem_univ ((1, 1) : ℝ × ℝ))
    (by norm_num)
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  norm_num [coupledValley] at midpoint

/-- Adding a nuisance-dependent offset preserves partial strong convexity but
destroys the shared restricted minimum. -/
noncomputable def shiftedValley (primary nuisance : ℝ) : ℝ :=
  coupledValley primary nuisance + nuisance ^ 2

/-- Without a shared restricted minimum, the partial-gradient PL conclusion
can fail even though the primary block remains a unit quadratic. -/
theorem sharedMinimum_is_loadBearing :
    ¬ 2 * 1 * (shiftedValley 1 1 - 0) ≤
      ‖coupledValleyPartialGradient 1 1‖ ^ 2 := by
  norm_num [shiftedValley, coupledValley, coupledValleyPartialGradient]

#print axioms partialGradient_sq_ge_twice_gap
#print axioms fullGradient_sq_ge_twice_gap
#print axioms nuisanceDrift_le_gap_add_quadratic
#print axioms gradientGapBound_is_loadBearing
#print axioms coupledValleyCertificate
#print axioms coupledValley_partialPL_exact
#print axioms coupledValley_not_strongConvexOn_product
#print axioms sharedMinimum_is_loadBearing

end PartialStrongConvexityPL

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
