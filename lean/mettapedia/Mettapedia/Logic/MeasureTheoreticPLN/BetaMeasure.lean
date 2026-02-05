import Mettapedia.Logic.MeasureTheoreticPLN.Basic
import Mathlib.Probability.Distributions.Beta

/-!
# Beta Measure for PLN Evidence

This file connects Mathlib's Beta distribution to PLN Evidence interpretation.

## Key Results

- `evidenceBetaMeasure`: Beta measure induced by Evidence and prior
- `evidenceBetaMeasure_isProbability`: It's a proper probability measure
- Connection between Evidence strength and Beta mean

## The Beta-Evidence Connection

Given evidence `e = (n⁺, n⁻)` with prior `(α₀, β₀)`:
- Posterior distribution is Beta(α₀ + n⁺, β₀ + n⁻)
- Posterior mean = (α₀ + n⁺) / (α₀ + β₀ + n⁺ + n⁻)
- As evidence grows, posterior concentrates around true θ

## References

- Mathlib.Probability.Distributions.Beta for the Beta distribution
- de Finetti's representation theorem for exchangeable sequences
-/

namespace Mettapedia.Logic.MeasureTheoreticPLN

open Mettapedia.Logic.EvidenceQuantale
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Re-exports from Mathlib -/

/-- The Beta normalizing constant B(α, β) = Γ(α)Γ(β)/Γ(α+β) -/
noncomputable abbrev betaNormConst := ProbabilityTheory.beta

/-- The Beta probability density function -/
noncomputable abbrev betaPdf := ProbabilityTheory.betaPDF

/-- The Beta probability measure on ℝ (concentrated on (0,1)) -/
noncomputable abbrev betaMeasureReal := ProbabilityTheory.betaMeasure

/-! ## Evidence-Induced Beta Measure -/

/-- Beta measure induced by Evidence with given interpretation.

    Given Evidence `e = (n⁺, n⁻)` and prior interpretation `(α₀, β₀)`,
    returns the Beta(α₀ + n⁺, β₀ + n⁻) measure.
-/
noncomputable def evidenceBetaMeasure (e : Evidence) (interp : EvidenceInterpretation)
    (hpos_fin : e.pos ≠ ⊤) (hneg_fin : e.neg ≠ ⊤) : Measure ℝ :=
  let bp := evidenceToBetaParams e interp hpos_fin hneg_fin
  betaMeasureReal bp.alpha bp.beta

/-- The evidence-induced Beta measure is a probability measure -/
theorem evidenceBetaMeasure_isProbability (e : Evidence) (interp : EvidenceInterpretation)
    (hpos_fin : e.pos ≠ ⊤) (hneg_fin : e.neg ≠ ⊤) :
    IsProbabilityMeasure (evidenceBetaMeasure e interp hpos_fin hneg_fin) := by
  unfold evidenceBetaMeasure
  let bp := evidenceToBetaParams e interp hpos_fin hneg_fin
  exact isProbabilityMeasureBeta bp.alpha_pos bp.beta_pos

/-! ## Prior Measures -/

/-- Uniform (Laplace) prior: Beta(1, 1) -/
noncomputable def uniformPriorMeasure : Measure ℝ :=
  betaMeasureReal 1 1

theorem uniformPriorMeasure_isProbability :
    IsProbabilityMeasure uniformPriorMeasure :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

/-- Jeffreys prior: Beta(0.5, 0.5) -/
noncomputable def jeffreysPriorMeasure : Measure ℝ :=
  betaMeasureReal 0.5 0.5

theorem jeffreysPriorMeasure_isProbability :
    IsProbabilityMeasure jeffreysPriorMeasure :=
  isProbabilityMeasureBeta (by norm_num) (by norm_num)

/-! ## Evidence from Natural Numbers -/

/-- Beta measure for evidence given as natural number counts -/
noncomputable def natEvidenceBetaMeasure (npos nneg : ℕ) (interp : EvidenceInterpretation) :
    Measure ℝ :=
  let e := evidenceFromNat npos nneg
  let hfin := evidenceFromNat_isFinite npos nneg
  evidenceBetaMeasure e interp hfin.1 hfin.2

theorem natEvidenceBetaMeasure_isProbability (npos nneg : ℕ) (interp : EvidenceInterpretation) :
    IsProbabilityMeasure (natEvidenceBetaMeasure npos nneg interp) := by
  unfold natEvidenceBetaMeasure
  apply evidenceBetaMeasure_isProbability

/-- Explicit formula: natEvidenceBetaMeasure uses Beta(α₀ + npos, β₀ + nneg) -/
theorem natEvidenceBetaMeasure_eq (npos nneg : ℕ) (interp : EvidenceInterpretation) :
    natEvidenceBetaMeasure npos nneg interp =
    betaMeasureReal (interp.prior_alpha + npos) (interp.prior_beta + nneg) := by
  unfold natEvidenceBetaMeasure evidenceBetaMeasure evidenceToBetaParams evidenceFromNat
  simp only [ENNReal.toReal_natCast]

/-! ## Beta Mean and Evidence Strength Connection -/

/-- The Beta mean α/(α+β) -/
noncomputable def betaMean (α β : ℝ) : ℝ := α / (α + β)

/-- Beta mean is in [0, 1] for positive parameters -/
theorem betaMean_mem_unit (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    betaMean α β ∈ Set.Icc (0 : ℝ) 1 := by
  unfold betaMean
  constructor
  · apply div_nonneg
    · linarith
    · linarith
  · rw [div_le_one (by linarith : 0 < α + β)]
    linarith

/-- The Evidence-induced Beta mean matches our BetaParams.mean -/
theorem evidenceBetaParams_mean_eq (e : Evidence) (interp : EvidenceInterpretation)
    (hpos_fin : e.pos ≠ ⊤) (hneg_fin : e.neg ≠ ⊤) :
    let bp := evidenceToBetaParams e interp hpos_fin hneg_fin
    bp.mean = betaMean bp.alpha bp.beta := by
  simp only [BetaParams.mean, BetaParams.total, betaMean]

/-! ## Summary

This file establishes:

1. **Re-exports from Mathlib**:
   - `betaNormConst`: Beta normalizing constant B(α,β)
   - `betaPdf`: Beta PDF
   - `betaMeasureReal`: Beta measure on ℝ

2. **Evidence-induced measures**:
   - `evidenceBetaMeasure`: Evidence + prior → Beta measure
   - `natEvidenceBetaMeasure`: Natural number evidence → Beta measure

3. **Prior measures**:
   - `uniformPriorMeasure`: Beta(1,1)
   - `jeffreysPriorMeasure`: Beta(0.5, 0.5)

4. **Beta mean**:
   - `betaMean`: The mean α/(α+β)
   - Connection to `BetaParams.mean`

## Next Steps

- `EvidenceSemantics.lean`: Define probability kernel Evidence → distributions
- Integration bounds connecting Beta mean to PLN strength
-/

end Mettapedia.Logic.MeasureTheoreticPLN
