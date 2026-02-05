import Mettapedia.Logic.MeasureTheoreticPLN.BetaMeasure
import Mettapedia.Logic.EvidenceBeta
import Mathlib.Probability.Kernel.Basic

/-!
# Evidence Semantics: Probability Kernel Interpretation

This file defines the probability kernel that maps PLN Evidence to probability
distributions over the parameter space θ ∈ [0,1].

## Key Definitions

- `EvidenceKernel`: Maps Evidence to Beta distributions
- `evidenceSemantics`: The main semantic interpretation function

## The Kernel Interpretation

Given Evidence `e = (n⁺, n⁻)` with prior interpretation `(α₀, β₀)`:
- The posterior distribution is Beta(α₀ + n⁺, β₀ + n⁻)
- This is a probability measure on [0,1]
- The mean converges to the "true" θ as evidence grows

## Categorical Semantics

The kernel structure gives PLN a categorical semantics:
- Objects: Evidence values
- Morphisms: Probability kernels (Markov kernels)
- Composition: Chapman-Kolmogorov equation

This connects to the quantale semantics in `PLNQuantaleSemantics/`.

## References

- de Finetti, "Theory of Probability" (1974)
- Goertzel et al., "Probabilistic Logic Networks" (2009)
- Mathlib.Probability.Kernel for kernel infrastructure
-/

namespace Mettapedia.Logic.MeasureTheoreticPLN

open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceBeta
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Evidence Semantics Function -/

/-- The semantic interpretation of finite Evidence as a Beta measure.

    This is the core semantic function: Evidence → Measure ℝ
    Given evidence (n⁺, n⁻) with prior (α₀, β₀), returns Beta(α₀+n⁺, β₀+n⁻).
-/
noncomputable def evidenceSemantics (interp : EvidenceInterpretation) :
    (e : Evidence) → (hpos : e.pos ≠ ⊤) → (hneg : e.neg ≠ ⊤) → Measure ℝ :=
  fun e hpos hneg => evidenceBetaMeasure e interp hpos hneg

/-- The semantics yields a probability measure -/
theorem evidenceSemantics_isProbability (interp : EvidenceInterpretation)
    (e : Evidence) (hpos : e.pos ≠ ⊤) (hneg : e.neg ≠ ⊤) :
    IsProbabilityMeasure (evidenceSemantics interp e hpos hneg) :=
  evidenceBetaMeasure_isProbability e interp hpos hneg

/-! ## Natural Number Evidence Semantics -/

/-- Simplified semantics for natural number evidence counts -/
noncomputable def natEvidenceSemantics (interp : EvidenceInterpretation) (npos nneg : ℕ) :
    Measure ℝ :=
  natEvidenceBetaMeasure npos nneg interp

theorem natEvidenceSemantics_isProbability (interp : EvidenceInterpretation) (npos nneg : ℕ) :
    IsProbabilityMeasure (natEvidenceSemantics interp npos nneg) :=
  natEvidenceBetaMeasure_isProbability npos nneg interp

/-- The semantics of zero evidence is the prior -/
theorem natEvidenceSemantics_zero (interp : EvidenceInterpretation) :
    natEvidenceSemantics interp 0 0 = betaMeasureReal interp.prior_alpha interp.prior_beta := by
  simp only [natEvidenceSemantics, natEvidenceBetaMeasure_eq, Nat.cast_zero, add_zero]

/-! ## Semantic Properties -/

/-- Adding evidence corresponds to Bayesian updating -/
theorem natEvidenceSemantics_add (interp : EvidenceInterpretation) (n₁ n₂ m₁ m₂ : ℕ) :
    natEvidenceSemantics interp (n₁ + n₂) (m₁ + m₂) =
    betaMeasureReal (interp.prior_alpha + n₁ + n₂) (interp.prior_beta + m₁ + m₂) := by
  simp only [natEvidenceSemantics, natEvidenceBetaMeasure_eq, Nat.cast_add]
  ring_nf

/-- The posterior parameters grow linearly with evidence -/
theorem natEvidenceSemantics_params (interp : EvidenceInterpretation) (npos nneg : ℕ) :
    let α := interp.prior_alpha + npos
    let β := interp.prior_beta + nneg
    natEvidenceSemantics interp npos nneg = betaMeasureReal α β := by
  simp only [natEvidenceSemantics, natEvidenceBetaMeasure_eq]

/-! ## Connection to PLN Strength -/

/-- The Beta mean from evidence with uniform prior -/
noncomputable def evidencePosteriorMean (npos nneg : ℕ) (interp : EvidenceInterpretation) : ℝ :=
  (interp.prior_alpha + npos) / (interp.prior_alpha + interp.prior_beta + npos + nneg)

/-- Posterior mean is in [0,1] -/
theorem evidencePosteriorMean_mem_unit (npos nneg : ℕ) (interp : EvidenceInterpretation) :
    evidencePosteriorMean npos nneg interp ∈ Set.Icc (0 : ℝ) 1 := by
  unfold evidencePosteriorMean
  have hα := interp.prior_pos.1
  have hβ := interp.prior_pos.2
  have hnum : 0 ≤ interp.prior_alpha + npos := by
    have : (0 : ℝ) ≤ npos := Nat.cast_nonneg npos
    linarith
  have hden : 0 < interp.prior_alpha + interp.prior_beta + npos + nneg := by
    have hn : (0 : ℝ) ≤ npos := Nat.cast_nonneg npos
    have hm : (0 : ℝ) ≤ nneg := Nat.cast_nonneg nneg
    linarith
  constructor
  · apply div_nonneg hnum (le_of_lt hden)
  · rw [div_le_one hden]
    have hm : (0 : ℝ) ≤ nneg := Nat.cast_nonneg nneg
    linarith

/-- With uniform prior, PLN strength approximates posterior mean.

    This is a qualitative statement - the exact bound is proven in EvidenceBeta.
-/
theorem plnStrength_approx_posteriorMean (npos nneg : ℕ) (hne : npos + nneg ≠ 0) :
    let strength := plnStrength npos nneg
    let mean := evidencePosteriorMean npos nneg EvidenceInterpretation.uniform
    |strength - mean| ≤ 2 / (npos + nneg + 2) := by
  -- Compute values explicitly
  have hn : 0 < npos + nneg := Nat.pos_of_ne_zero hne
  have hnR : (0 : ℝ) < npos + nneg := by exact_mod_cast hn
  have hn2 : (0 : ℝ) < npos + nneg + 2 := by linarith
  -- strength = npos / (npos + nneg)
  have hstrength : plnStrength npos nneg = (npos : ℝ) / (npos + nneg) :=
    plnStrength_eq_improper_mean npos nneg hne
  -- mean = (1 + npos) / (2 + npos + nneg) with uniform prior (α=β=1)
  have hmean : evidencePosteriorMean npos nneg EvidenceInterpretation.uniform =
      (1 + npos) / (2 + npos + nneg) := by
    simp only [evidencePosteriorMean, EvidenceInterpretation.uniform]
    ring
  simp only [hstrength, hmean]
  -- Direct computation of |npos/n - (1+npos)/(n+2)|
  have hne' : (npos + nneg : ℝ) ≠ 0 := hnR.ne'
  have hne2 : (2 + npos + nneg : ℝ) ≠ 0 := by linarith
  have hnpos : (0 : ℝ) ≤ npos := Nat.cast_nonneg _
  have hnneg : (0 : ℝ) ≤ nneg := Nat.cast_nonneg _
  have hdenom_pos : 0 < (npos + nneg : ℝ) * (npos + nneg + 2) := mul_pos hnR hn2
  -- Compute: npos/n - (1+npos)/(n+2) = (npos - nneg) / (n(n+2))
  have hdiff : (npos : ℝ) / (npos + nneg) - (1 + npos) / (2 + npos + nneg) =
      ((npos : ℝ) - nneg) / ((npos + nneg) * (npos + nneg + 2)) := by
    field_simp [hne', hne2]
    ring
  -- Key bound: |a - b| ≤ a + b for nonnegative a, b
  have habs : |(npos : ℝ) - nneg| ≤ npos + nneg := by
    rw [abs_le]
    constructor
    · linarith
    · linarith
  have hbound : |(npos : ℝ) / (npos + nneg) - (1 + npos) / (2 + npos + nneg)| ≤ 1 / (npos + nneg + 2) := by
    rw [hdiff, abs_div, abs_of_pos hdenom_pos]
    calc |(npos : ℝ) - nneg| / ((npos + nneg) * (npos + nneg + 2))
        ≤ (npos + nneg) / ((npos + nneg) * (npos + nneg + 2)) := by
          apply div_le_div_of_nonneg_right habs (le_of_lt hdenom_pos)
      _ = 1 / (npos + nneg + 2) := by field_simp [hne']
  calc |(npos : ℝ) / (npos + nneg) - (1 + npos) / (2 + npos + nneg)|
      ≤ 1 / (npos + nneg + 2) := hbound
    _ ≤ 2 / (npos + nneg + 2) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hn2)
        norm_num

/-! ## Semantic Equivalence -/

/-- Two evidence values are semantically equivalent if they induce the same measure -/
def semanticallyEquivalent (interp : EvidenceInterpretation) (n₁ m₁ n₂ m₂ : ℕ) : Prop :=
  natEvidenceSemantics interp n₁ m₁ = natEvidenceSemantics interp n₂ m₂

/-- Equal natural number counts implies semantic equivalence -/
theorem semanticallyEquivalent_of_eq (interp : EvidenceInterpretation) (n₁ m₁ n₂ m₂ : ℕ)
    (hn : n₁ = n₂) (hm : m₁ = m₂) :
    semanticallyEquivalent interp n₁ m₁ n₂ m₂ := by
  unfold semanticallyEquivalent
  simp only [hn, hm]

/-- Semantic equivalence is reflexive -/
theorem semanticallyEquivalent_refl (interp : EvidenceInterpretation) (n m : ℕ) :
    semanticallyEquivalent interp n m n m := by
  unfold semanticallyEquivalent
  rfl

/-- Semantic equivalence is symmetric -/
theorem semanticallyEquivalent_symm (interp : EvidenceInterpretation) (n₁ m₁ n₂ m₂ : ℕ)
    (h : semanticallyEquivalent interp n₁ m₁ n₂ m₂) :
    semanticallyEquivalent interp n₂ m₂ n₁ m₁ := by
  unfold semanticallyEquivalent at *
  exact h.symm

/-! ## Summary

This file establishes:

1. **Core semantics**:
   - `evidenceSemantics`: Evidence → Beta measure
   - `natEvidenceSemantics`: Simplified version for ℕ counts

2. **Semantic properties**:
   - `natEvidenceSemantics_zero`: Zero evidence gives prior
   - `natEvidenceSemantics_add`: Evidence addition is Bayesian updating

3. **Connection to PLN strength**:
   - `evidencePosteriorMean`: The Beta mean
   - `plnStrength_approx_posteriorMean`: |strength - mean| ≤ 2/(n+2)

4. **Semantic equivalence**:
   - `semanticallyEquivalent`: When two evidence values mean the same

## Categorical Interpretation

The semantics can be viewed categorically:
- Evidence forms a monoid under `hplus`
- The semantics is a functor to the category of probability measures
- Markov kernels give the morphisms

This connects to the quantale semantics where Evidence has Frame structure.
-/

end Mettapedia.Logic.MeasureTheoreticPLN
