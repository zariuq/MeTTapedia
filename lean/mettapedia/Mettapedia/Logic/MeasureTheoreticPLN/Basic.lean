import Mettapedia.Logic.PLNEvidence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.UnitInterval

/-!
# Measure-Theoretic PLN Semantics: Basic Definitions

This file establishes the core definitions connecting PLN Evidence to measure-theoretic
probability via the Beta distribution interpretation.

## Key Definitions

- `EvidenceInterpretation`: Parameters specifying how Evidence maps to Beta distributions
- `Evidence.toBetaParams`: Convert Evidence (n⁺, n⁻) to Beta(α, β) parameters
- `ThetaSpace`: The sample space [0,1] for Bernoulli parameter θ

## The Main Interpretation

Evidence `(n⁺, n⁻)` represents:
- `n⁺` positive observations (successes)
- `n⁻` negative observations (failures)

With prior pseudo-counts `(α₀, β₀)`, this induces a Beta distribution:
- Beta(α₀ + n⁺, β₀ + n⁻)

The standard prior choices are:
- Uniform (Laplace): α₀ = β₀ = 1
- Jeffreys: α₀ = β₀ = 0.5
- Improper (Haldane): α₀ = β₀ → 0 (limiting case)

## References

- de Finetti, "Theory of Probability" (1974)
- Goertzel et al., "Probabilistic Logic Networks" (2009)
- Existing `EvidenceBeta.lean` for the convergence bounds
-/

namespace Mettapedia.Logic.MeasureTheoreticPLN

open Mettapedia.Logic.PLNEvidence
open MeasureTheory
open scoped ENNReal NNReal unitInterval

/-! ## Sample Space -/

/-- The sample space for Bernoulli parameter θ: the unit interval [0,1].

    This is the support of the Beta distribution representing our belief about
    the "true" probability underlying the observed evidence.
-/
abbrev ThetaSpace := Set.Icc (0 : ℝ) 1

/-- ThetaSpace is nonempty (contains 0 and 1) -/
theorem thetaSpace_nonempty : (Set.Icc (0 : ℝ) 1).Nonempty := Set.nonempty_Icc.mpr (by norm_num)

/-! ## Evidence Interpretation Parameters -/

/-- Parameters specifying how Evidence maps to probability distributions.

    The key parameters are the prior pseudo-counts for the Beta distribution:
    - `prior_alpha`: pseudo-count for positive evidence (α₀)
    - `prior_beta`: pseudo-count for negative evidence (β₀)

    Common choices:
    - Uniform prior: α₀ = β₀ = 1
    - Jeffreys prior: α₀ = β₀ = 0.5
-/
structure EvidenceInterpretation where
  /-- Prior pseudo-count for positive evidence (α₀ in Beta prior) -/
  prior_alpha : ℝ
  /-- Prior pseudo-count for negative evidence (β₀ in Beta prior) -/
  prior_beta : ℝ
  /-- Prior parameters must be positive for proper Beta distribution -/
  prior_pos : 0 < prior_alpha ∧ 0 < prior_beta

namespace EvidenceInterpretation

/-- The uniform (Laplace) prior: Beta(1, 1) -/
def uniform : EvidenceInterpretation where
  prior_alpha := 1
  prior_beta := 1
  prior_pos := ⟨by norm_num, by norm_num⟩

/-- The Jeffreys prior: Beta(0.5, 0.5) -/
def jeffreys : EvidenceInterpretation where
  prior_alpha := 0.5
  prior_beta := 0.5
  prior_pos := ⟨by norm_num, by norm_num⟩

/-- A general symmetric prior: Beta(k, k) for any k > 0 -/
def symmetric (k : ℝ) (hk : 0 < k) : EvidenceInterpretation where
  prior_alpha := k
  prior_beta := k
  prior_pos := ⟨hk, hk⟩

/-- Total prior pseudo-counts: α₀ + β₀ -/
noncomputable def totalPrior (interp : EvidenceInterpretation) : ℝ :=
  interp.prior_alpha + interp.prior_beta

/-- Total prior is positive -/
theorem totalPrior_pos (interp : EvidenceInterpretation) : 0 < interp.totalPrior := by
  unfold totalPrior
  linarith [interp.prior_pos.1, interp.prior_pos.2]

end EvidenceInterpretation

/-! ## Converting Evidence to Beta Parameters -/

/-- Beta distribution parameters derived from Evidence and prior.

    Given Evidence `(n⁺, n⁻)` and prior `(α₀, β₀)`:
    - α = α₀ + n⁺
    - β = β₀ + n⁻
-/
structure BetaParams where
  /-- α parameter (shape for success) -/
  alpha : ℝ
  /-- β parameter (shape for failure) -/
  beta : ℝ
  /-- α must be positive -/
  alpha_pos : 0 < alpha
  /-- β must be positive -/
  beta_pos : 0 < beta

namespace BetaParams

/-- Total concentration: α + β -/
noncomputable def total (p : BetaParams) : ℝ := p.alpha + p.beta

/-- Total is positive -/
theorem total_pos (p : BetaParams) : 0 < p.total := by
  unfold total
  linarith [p.alpha_pos, p.beta_pos]

/-- Beta mean: α / (α + β) -/
noncomputable def mean (p : BetaParams) : ℝ := p.alpha / p.total

/-- Beta mean is in [0, 1] -/
theorem mean_mem_unit (p : BetaParams) : p.mean ∈ Set.Icc (0 : ℝ) 1 := by
  unfold mean total
  constructor
  · apply div_nonneg
    · linarith [p.alpha_pos]
    · linarith [p.alpha_pos, p.beta_pos]
  · rw [div_le_one (by linarith [p.alpha_pos, p.beta_pos])]
    have hbeta : 0 < p.beta := p.beta_pos
    linarith [hbeta]

/-- Beta variance: αβ / ((α+β)²(α+β+1)) -/
noncomputable def variance (p : BetaParams) : ℝ :=
  (p.alpha * p.beta) / (p.total ^ 2 * (p.total + 1))

/-- Variance is non-negative -/
theorem variance_nonneg (p : BetaParams) : 0 ≤ p.variance := by
  unfold variance total
  apply div_nonneg
  · apply mul_nonneg <;> linarith [p.alpha_pos, p.beta_pos]
  · apply mul_nonneg
    · apply sq_nonneg
    · linarith [p.alpha_pos, p.beta_pos]

end BetaParams

/-! ## Evidence to Beta Conversion -/

/-- Convert Evidence to Beta parameters with given prior.

    Given evidence `e = (n⁺, n⁻)` and interpretation `interp = (α₀, β₀)`:
    Returns BetaParams with α = α₀ + n⁺, β = β₀ + n⁻

    Requires: n⁺ and n⁻ are finite (not ⊤)
-/
noncomputable def evidenceToBetaParams (e : Evidence) (interp : EvidenceInterpretation)
    (_hpos_fin : e.pos ≠ ⊤) (_hneg_fin : e.neg ≠ ⊤) : BetaParams where
  alpha := interp.prior_alpha + e.pos.toReal
  beta := interp.prior_beta + e.neg.toReal
  alpha_pos := by
    have h : 0 ≤ e.pos.toReal := ENNReal.toReal_nonneg
    linarith [interp.prior_pos.1]
  beta_pos := by
    have h : 0 ≤ e.neg.toReal := ENNReal.toReal_nonneg
    linarith [interp.prior_pos.2]

/-- The Beta mean from evidence equals PLN strength asymptotically.

    For evidence `(n⁺, n⁻)` with total n = n⁺ + n⁻:
    - PLN strength = n⁺/n
    - Beta mean = (α₀ + n⁺)/(α₀ + β₀ + n)

    As n → ∞, the difference → 0 at rate O(1/n).

    This is proven more carefully in `EvidenceBeta.lean`.
-/
theorem evidenceToBetaParams_mean (e : Evidence) (interp : EvidenceInterpretation)
    (hpos_fin : e.pos ≠ ⊤) (hneg_fin : e.neg ≠ ⊤) :
    let bp := evidenceToBetaParams e interp hpos_fin hneg_fin
    bp.mean = (interp.prior_alpha + e.pos.toReal) /
              (interp.totalPrior + e.total.toReal) := by
  simp only [evidenceToBetaParams, BetaParams.mean, BetaParams.total,
             EvidenceInterpretation.totalPrior]
  congr 1
  unfold Evidence.total
  rw [ENNReal.toReal_add hpos_fin hneg_fin]
  ring

/-- Evidence with finite components yields well-defined Beta parameters -/
theorem evidenceToBetaParams_total (e : Evidence) (interp : EvidenceInterpretation)
    (hpos_fin : e.pos ≠ ⊤) (hneg_fin : e.neg ≠ ⊤) :
    (evidenceToBetaParams e interp hpos_fin hneg_fin).total =
    interp.totalPrior + e.total.toReal := by
  simp only [evidenceToBetaParams, BetaParams.total, EvidenceInterpretation.totalPrior,
             Evidence.total]
  rw [ENNReal.toReal_add hpos_fin hneg_fin]
  ring

/-! ## Finite Evidence -/

/-- Predicate for evidence with finite components (necessary for measure-theoretic interpretation) -/
def EvidenceIsFinite (e : Evidence) : Prop := e.pos ≠ ⊤ ∧ e.neg ≠ ⊤

/-- Zero evidence is finite -/
theorem evidenceIsFinite_zero : EvidenceIsFinite Evidence.zero := by
  simp [EvidenceIsFinite, Evidence.zero]

/-- One evidence is finite -/
theorem evidenceIsFinite_one : EvidenceIsFinite Evidence.one := by
  simp [EvidenceIsFinite, Evidence.one]

/-- hplus preserves finiteness when both inputs are finite -/
theorem evidenceIsFinite_hplus {e₁ e₂ : Evidence} (h₁ : EvidenceIsFinite e₁) (h₂ : EvidenceIsFinite e₂) :
    EvidenceIsFinite (e₁ + e₂) := by
  simp only [EvidenceIsFinite, Evidence.hplus_def] at *
  constructor
  · exact ENNReal.add_ne_top.mpr ⟨h₁.1, h₂.1⟩
  · exact ENNReal.add_ne_top.mpr ⟨h₁.2, h₂.2⟩

/-- Construct evidence from natural numbers (always finite) -/
def evidenceFromNat (npos nneg : ℕ) : Evidence := ⟨npos, nneg⟩

/-- Evidence from natural numbers is finite -/
theorem evidenceFromNat_isFinite (npos nneg : ℕ) : EvidenceIsFinite (evidenceFromNat npos nneg) := by
  unfold EvidenceIsFinite evidenceFromNat
  constructor <;> exact ENNReal.natCast_ne_top _

/-! ## Summary

This file establishes:

1. **ThetaSpace**: The sample space [0,1] for Bernoulli parameter θ

2. **EvidenceInterpretation**: Prior parameters (α₀, β₀) for Beta distribution
   - `uniform`: Laplace prior (1, 1)
   - `jeffreys`: Jeffreys prior (0.5, 0.5)

3. **BetaParams**: Parameters (α, β) for Beta distribution with:
   - `mean`: Expected value α/(α+β)
   - `variance`: Variance αβ/((α+β)²(α+β+1))

4. **Evidence.toBetaParams**: Convert evidence (n⁺, n⁻) to Beta(α₀+n⁺, β₀+n⁻)

5. **Evidence.IsFinite**: Predicate for finite evidence (required for measure-theoretic ops)

## Next Steps

- `BetaMeasure.lean`: Construct the actual Beta measure on [0,1]
- `EvidenceSemantics.lean`: Define the probability kernel Evidence → Measure ThetaSpace
- Integration with Convergence module for LLN proofs
-/

end Mettapedia.Logic.MeasureTheoreticPLN
