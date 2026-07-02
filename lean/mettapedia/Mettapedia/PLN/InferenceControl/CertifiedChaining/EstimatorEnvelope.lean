import Mathlib.Tactic
import Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeductionITVBridge

/-!
# Estimator-in-envelope selectors for certified PLN chaining

This module proves the yes-go counterpart to the certified-chaining no-go
theorems: a learned selector may choose a sharper point estimate, but only as a
convex mixture of already certified in-envelope points.
-/

namespace Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope

open scoped BigOperators ENNReal
open Mettapedia.Logic.HOL
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
open Mettapedia.PLN.TruthValues.PLNIndefiniteTruth

noncomputable section

universe u v

/-! ## Phase 1: generic envelope soundness -/

/-- A selector is any estimator output already certified to be a unit-interval
mixing weight. -/
structure EnvelopeSelector where
  weight : ℝ
  weight_mem_unit : weight ∈ Set.Icc (0 : ℝ) 1

namespace EnvelopeSelector

/-- The selected point between a preferred point `x` and fallback point `y`. -/
def select (selector : EnvelopeSelector) (x y : ℝ) : ℝ :=
  selector.weight * x + (1 - selector.weight) * y

/-- Build a selector from `BinaryEvidence.toStrength`. -/
def ofBinaryEvidence (e : BinaryEvidence) : EnvelopeSelector where
  weight := (BinaryEvidence.toStrength e).toReal
  weight_mem_unit := by
    constructor
    · exact ENNReal.toReal_nonneg
    · have h := BinaryEvidence.toStrength_le_one e
      have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) := by simp
      rw [h1] at h
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h

/-- Thin constructor from the shared derivation-tree grading fold. -/
def ofGradeWith
    {Base : Type u} {Const : Ty Base → Type v}
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (payload : DerivationTree.GradePayload Const BinaryEvidence)
    (d : DerivationTree Const Δ φ) : EnvelopeSelector :=
  ofBinaryEvidence (DerivationTree.gradeWith payload d)

/-- Thin constructor from the formula-level BinaryEvidence readout. -/
def ofFormulaEvGrade
    {Base : Type u} {Const : Ty Base → Type v}
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const) : EnvelopeSelector :=
  ofBinaryEvidence
    (Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.formulaEvGrade
      (Const := Const) T φ)

theorem select_weight_one_eq_left
    (selector : EnvelopeSelector) (h : selector.weight = 1) (x y : ℝ) :
    selector.select x y = x := by
  simp [select, h]

end EnvelopeSelector

/-- Real-valued view of an ENNReal quotient. -/
theorem ennreal_toReal_div (a b : ℝ≥0∞) :
    (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv, ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv]

/-- Real-valued `toStrength` as the ordinary quotient by total evidence when
the total is nonzero. -/
theorem toReal_toStrength_eq_pos_div_total
    (e : BinaryEvidence) (htotal : e.total ≠ 0) :
    (BinaryEvidence.toStrength e).toReal = e.pos.toReal / e.total.toReal := by
  unfold BinaryEvidence.toStrength
  simp [htotal]

/-- The midpoint representative of an ITV lies inside its interval. -/
theorem itv_strength_mem_bounds (itv : ITV) :
    itv.lower ≤ itv.strength ∧ itv.strength ≤ itv.upper := by
  unfold ITV.strength
  constructor <;> nlinarith [itv.lower_le_upper]

/-- Intervals are convex: any unit-weight mixture of two in-interval points is
again in the interval. -/
theorem itv_convex_mix_mem_bounds
    (itv : ITV) {q x y : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : itv.lower ≤ x ∧ x ≤ itv.upper)
    (hy : itv.lower ≤ y ∧ y ≤ itv.upper) :
    itv.lower ≤ q * x + (1 - q) * y ∧
      q * x + (1 - q) * y ≤ itv.upper := by
  have hq0 : 0 ≤ q := hq.1
  have hq1 : q ≤ 1 := hq.2
  have h1q0 : 0 ≤ 1 - q := by linarith
  constructor
  · have hx_low : q * itv.lower ≤ q * x :=
      mul_le_mul_of_nonneg_left hx.1 hq0
    have hy_low : (1 - q) * itv.lower ≤ (1 - q) * y :=
      mul_le_mul_of_nonneg_left hy.1 h1q0
    nlinarith
  · have hx_up : q * x ≤ q * itv.upper :=
      mul_le_mul_of_nonneg_left hx.2 hq0
    have hy_up : (1 - q) * y ≤ (1 - q) * itv.upper :=
      mul_le_mul_of_nonneg_left hy.2 h1q0
    nlinarith

namespace EnvelopeSelector

/-- A selector between two certified in-envelope points remains in-envelope. -/
theorem select_mem_ITV
    (selector : EnvelopeSelector) (itv : ITV) {x y : ℝ}
    (hx : itv.lower ≤ x ∧ x ≤ itv.upper)
    (hy : itv.lower ≤ y ∧ y ≤ itv.upper) :
    itv.lower ≤ selector.select x y ∧
      selector.select x y ≤ itv.upper :=
  itv_convex_mix_mem_bounds itv selector.weight_mem_unit hx hy

/-- A selector between one certified point and the ITV midpoint remains
in-envelope. -/
theorem select_point_midpoint_mem_ITV
    (selector : EnvelopeSelector) (itv : ITV) {x : ℝ}
    (hx : itv.lower ≤ x ∧ x ≤ itv.upper) :
    itv.lower ≤ selector.select x itv.strength ∧
      selector.select x itv.strength ≤ itv.upper :=
  selector.select_mem_ITV itv hx (itv_strength_mem_bounds itv)

end EnvelopeSelector

/-! ## Phase 1: deduction specialization -/

/-- Deduction strength selected between the PLN point formula and the midpoint
of the existing deduction credal ITV. -/
def selectedDeductionStrength
    (selector : EnvelopeSelector)
    (pA pB pC sAB sBC : ℝ)
    (hpA : 0 < pA)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  let itv :=
    deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
  selector.select (simpleDeductionStrengthFormula pA pB pC sAB sBC)
    itv.strength

/-- No estimator can escape the deduction credal envelope: once the PLN point
formula is certified in the existing deduction ITV, mixing it with the midpoint
is certified for every selector. -/
theorem selectedDeductionStrength_mem_deductionCredalStrengthITV
    (selector : EnvelopeSelector)
    (pA pB pC sAB sBC : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (h_consist :
      conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC)
    (ht_lower :
      deductionBBranchLower pA pB sAB sBC ≤ pA * sAB * sBC)
    (ht_upper :
      pA * sAB * sBC ≤ deductionBBranchUpper pA pB sAB sBC)
    (hu_lower :
      deductionNotBBranchLower pA pB pC sAB sBC ≤
        pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC)
    (hu_upper :
      pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC ≤
        deductionNotBBranchUpper pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
    itv.lower ≤ selectedDeductionStrength selector pA pB pC sAB sBC
      hpA hFeas credibility hc ∧
    selectedDeductionStrength selector pA pB pC sAB sBC hpA hFeas
      credibility hc ≤ itv.upper := by
  dsimp [selectedDeductionStrength]
  exact selector.select_point_midpoint_mem_ITV _
    (simpleDeductionStrengthFormula_mem_deductionCredalStrengthITV
      pA pB pC sAB sBC hpA hpB_small hFeas h_consist ht_lower ht_upper
      hu_lower hu_upper credibility hc)

/-! ## Phase 2: derived independence-event decomposition and evidence weld -/

/-- A finite two-branch probability model for the independence side condition
`S`: either the side condition holds, or its complement holds. -/
structure BooleanEventWeights where
  pS : ℝ
  pNotS : ℝ
  pS_nonneg : 0 ≤ pS
  pNotS_nonneg : 0 ≤ pNotS
  sum_eq_one : pS + pNotS = 1

namespace BooleanEventWeights

theorem pS_le_one (w : BooleanEventWeights) : w.pS ≤ 1 := by
  nlinarith [w.pNotS_nonneg, w.sum_eq_one]

theorem pS_mem_unit (w : BooleanEventWeights) :
    w.pS ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨w.pS_nonneg, w.pS_le_one⟩

theorem pNotS_eq_one_sub (w : BooleanEventWeights) :
    w.pNotS = 1 - w.pS := by
  linarith [w.sum_eq_one]

def toSelector (w : BooleanEventWeights) : EnvelopeSelector where
  weight := w.pS
  weight_mem_unit := w.pS_mem_unit

end BooleanEventWeights

/-- Finite total expectation over the two branches `S` and `not S`. -/
def twoBranchExpectation (w : BooleanEventWeights) (value : Bool → ℝ) : ℝ :=
  w.pS * value true + w.pNotS * value false

/-- Law of total expectation for the finite independence-event split.  Under
`S`, the branch value is the derived PLN point formula; under `not S`, the
branch value is the residual conditional mean. -/
theorem twoBranchExpectation_eq_independence_decomposition
    (w : BooleanEventWeights) (value : Bool → ℝ) (point residual : ℝ)
    (hS : value true = point)
    (hNotS : value false = residual) :
    twoBranchExpectation w value =
      w.pS * point + (1 - w.pS) * residual := by
  simp [twoBranchExpectation, hS, hNotS, w.pNotS_eq_one_sub]

/-- `EnvelopeSelector.select` is the two-branch total-expectation
decomposition instantiated with `q = P(S)`. -/
theorem EnvelopeSelector.select_eq_twoBranchExpectation
    (w : BooleanEventWeights) (value : Bool → ℝ) (point residual : ℝ)
    (hS : value true = point)
    (hNotS : value false = residual) :
    (w.toSelector).select point residual = twoBranchExpectation w value := by
  rw [twoBranchExpectation_eq_independence_decomposition w value point residual hS hNotS]
  rfl

/-- Derived posterior mean for deduction once the `not S` residual has been
supplied.  This is the finite abstract counterpart of the full measure-model
total-expectation derivation. -/
def derivedDeductionPosteriorMean
    (w : BooleanEventWeights)
    (pA pB pC sAB sBC residual : ℝ) : ℝ :=
  (w.toSelector).select
    (simpleDeductionStrengthFormula pA pB pC sAB sBC)
    residual

theorem derivedDeductionPosteriorMean_eq_twoBranchExpectation
    (w : BooleanEventWeights) (value : Bool → ℝ)
    (pA pB pC sAB sBC residual : ℝ)
    (hS :
      value true = simpleDeductionStrengthFormula pA pB pC sAB sBC)
    (hNotS : value false = residual) :
    derivedDeductionPosteriorMean w pA pB pC sAB sBC residual =
      twoBranchExpectation w value := by
  exact EnvelopeSelector.select_eq_twoBranchExpectation w value
    (simpleDeductionStrengthFormula pA pB pC sAB sBC) residual hS hNotS

/-- If the residual `not S` conditional mean is in the deduction envelope, then
the derived two-branch posterior mean is in the same envelope. -/
theorem derivedDeductionPosteriorMean_mem_deductionCredalStrengthITV
    (w : BooleanEventWeights)
    (pA pB pC sAB sBC residual : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (h_consist :
      conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC)
    (ht_lower :
      deductionBBranchLower pA pB sAB sBC ≤ pA * sAB * sBC)
    (ht_upper :
      pA * sAB * sBC ≤ deductionBBranchUpper pA pB sAB sBC)
    (hu_lower :
      deductionNotBBranchLower pA pB pC sAB sBC ≤
        pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC)
    (hu_upper :
      pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC ≤
        deductionNotBBranchUpper pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1)
    (hResidual :
      let itv :=
        deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
      itv.lower ≤ residual ∧ residual ≤ itv.upper) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
    itv.lower ≤
        derivedDeductionPosteriorMean w pA pB pC sAB sBC residual ∧
      derivedDeductionPosteriorMean w pA pB pC sAB sBC residual ≤
        itv.upper := by
  dsimp [derivedDeductionPosteriorMean] at hResidual ⊢
  exact (w.toSelector).select_mem_ITV _
    (simpleDeductionStrengthFormula_mem_deductionCredalStrengthITV
      pA pB pC sAB sBC hpA hpB_small hFeas h_consist ht_lower ht_upper
      hu_lower hu_upper credibility hc)
    hResidual

/-- Evidence readout used as an estimator of the total-expectation mixing
weight `P(S)`, with the `not S` residual conditional mean supplied explicitly. -/
def evidenceEstimatedDeductionPosteriorMean
    (sideEvidence : BinaryEvidence)
    (pA pB pC sAB sBC residual : ℝ) : ℝ :=
  (EnvelopeSelector.ofBinaryEvidence sideEvidence).select
    (simpleDeductionStrengthFormula pA pB pC sAB sBC)
    residual

/-- If the BinaryEvidence readout matches the independence-event probability,
the evidence estimate is exactly the finite total-expectation posterior mean. -/
theorem evidenceEstimatedDeductionPosteriorMean_eq_derived
    (sideEvidence : BinaryEvidence)
    (w : BooleanEventWeights)
    (pA pB pC sAB sBC residual : ℝ)
    (hweight : (BinaryEvidence.toStrength sideEvidence).toReal = w.pS) :
    evidenceEstimatedDeductionPosteriorMean sideEvidence
      pA pB pC sAB sBC residual =
      derivedDeductionPosteriorMean w pA pB pC sAB sBC residual := by
  unfold evidenceEstimatedDeductionPosteriorMean derivedDeductionPosteriorMean
  unfold EnvelopeSelector.ofBinaryEvidence BooleanEventWeights.toSelector
  unfold EnvelopeSelector.select
  dsimp
  rw [hweight]

/-- The evidence-estimated posterior mean remains inside the deduction envelope
whenever its explicit residual branch is in the envelope. -/
theorem evidenceEstimatedDeductionPosteriorMean_mem_deductionCredalStrengthITV
    (sideEvidence : BinaryEvidence)
    (pA pB pC sAB sBC residual : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (h_consist :
      conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC)
    (ht_lower :
      deductionBBranchLower pA pB sAB sBC ≤ pA * sAB * sBC)
    (ht_upper :
      pA * sAB * sBC ≤ deductionBBranchUpper pA pB sAB sBC)
    (hu_lower :
      deductionNotBBranchLower pA pB pC sAB sBC ≤
        pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC)
    (hu_upper :
      pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC ≤
        deductionNotBBranchUpper pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1)
    (hResidual :
      let itv :=
        deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
      itv.lower ≤ residual ∧ residual ≤ itv.upper) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
    itv.lower ≤
        evidenceEstimatedDeductionPosteriorMean sideEvidence
          pA pB pC sAB sBC residual ∧
      evidenceEstimatedDeductionPosteriorMean sideEvidence
          pA pB pC sAB sBC residual ≤ itv.upper := by
  dsimp [evidenceEstimatedDeductionPosteriorMean] at hResidual ⊢
  exact (EnvelopeSelector.ofBinaryEvidence sideEvidence).select_mem_ITV _
    (simpleDeductionStrengthFormula_mem_deductionCredalStrengthITV
      pA pB pC sAB sBC hpA hpB_small hFeas h_consist ht_lower ht_upper
      hu_lower hu_upper credibility hc)
    hResidual

/-- Boundary case: when the readout estimates `P(S)=1`, the posterior mean
recovers the derived point formula, independently of the residual branch. -/
theorem evidenceEstimatedDeductionPosteriorMean_crisp_one_eq_formula
    (sideEvidence : BinaryEvidence)
    (hcrisp : (BinaryEvidence.toStrength sideEvidence).toReal = 1)
    (pA pB pC sAB sBC residual : ℝ) :
    evidenceEstimatedDeductionPosteriorMean sideEvidence
      pA pB pC sAB sBC residual =
      simpleDeductionStrengthFormula pA pB pC sAB sBC := by
  unfold evidenceEstimatedDeductionPosteriorMean
  unfold EnvelopeSelector.ofBinaryEvidence EnvelopeSelector.select
  dsimp
  rw [hcrisp]
  ring

/-- Deduction strength selected by an evidence-based estimate of `P(S)`, using
the ITV midpoint as an explicitly sound default for an unmodeled `not S`
residual. -/
def evidenceSelectedDeductionStrength
    (sideEvidence : BinaryEvidence)
    (pA pB pC sAB sBC : ℝ)
    (hpA : 0 < pA)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) : ℝ :=
  selectedDeductionStrength (EnvelopeSelector.ofBinaryEvidence sideEvidence)
    pA pB pC sAB sBC hpA hFeas credibility hc

theorem evidenceSelectedDeductionStrength_mem_deductionCredalStrengthITV
    (sideEvidence : BinaryEvidence)
    (pA pB pC sAB sBC : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (h_consist :
      conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC)
    (ht_lower :
      deductionBBranchLower pA pB sAB sBC ≤ pA * sAB * sBC)
    (ht_upper :
      pA * sAB * sBC ≤ deductionBBranchUpper pA pB sAB sBC)
    (hu_lower :
      deductionNotBBranchLower pA pB pC sAB sBC ≤
        pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC)
    (hu_upper :
      pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC ≤
        deductionNotBBranchUpper pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
    itv.lower ≤ evidenceSelectedDeductionStrength sideEvidence
      pA pB pC sAB sBC hpA hFeas credibility hc ∧
    evidenceSelectedDeductionStrength sideEvidence pA pB pC sAB sBC
      hpA hFeas credibility hc ≤ itv.upper :=
  selectedDeductionStrength_mem_deductionCredalStrengthITV
    (EnvelopeSelector.ofBinaryEvidence sideEvidence)
    pA pB pC sAB sBC hpA hpB_small hFeas h_consist
    ht_lower ht_upper hu_lower hu_upper credibility hc

/-- Thin corollary for any BinaryEvidence-valued derivation-tree payload. -/
theorem gradeWithSelectedDeductionStrength_mem_deductionCredalStrengthITV
    {Base : Type u} {Const : Ty Base → Type v}
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (payload : DerivationTree.GradePayload Const BinaryEvidence)
    (d : DerivationTree Const Δ φ)
    (pA pB pC sAB sBC : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (h_consist :
      conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC)
    (ht_lower :
      deductionBBranchLower pA pB sAB sBC ≤ pA * sAB * sBC)
    (ht_upper :
      pA * sAB * sBC ≤ deductionBBranchUpper pA pB sAB sBC)
    (hu_lower :
      deductionNotBBranchLower pA pB pC sAB sBC ≤
        pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC)
    (hu_upper :
      pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC ≤
        deductionNotBBranchUpper pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
    itv.lower ≤ evidenceSelectedDeductionStrength
      (DerivationTree.gradeWith payload d) pA pB pC sAB sBC hpA hFeas
      credibility hc ∧
    evidenceSelectedDeductionStrength (DerivationTree.gradeWith payload d)
      pA pB pC sAB sBC hpA hFeas credibility hc ≤ itv.upper :=
  evidenceSelectedDeductionStrength_mem_deductionCredalStrengthITV
    (DerivationTree.gradeWith payload d) pA pB pC sAB sBC hpA hpB_small
    hFeas h_consist ht_lower ht_upper hu_lower hu_upper credibility hc

/-- Thin corollary for the formula-level BinaryEvidence readout. -/
theorem formulaEvGradeSelectedDeductionStrength_mem_deductionCredalStrengthITV
    {Base : Type u} {Const : Ty Base → Type v}
    (T : ClosedTheorySet Const) (φ : ClosedFormula Const)
    (pA pB pC sAB sBC : ℝ)
    (hpA : 0 < pA)
    (hpB_small : pB ≤ 0.99)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (h_consist :
      conditionalProbabilityConsistency pA pB sAB ∧
      conditionalProbabilityConsistency pB pC sBC)
    (ht_lower :
      deductionBBranchLower pA pB sAB sBC ≤ pA * sAB * sBC)
    (ht_upper :
      pA * sAB * sBC ≤ deductionBBranchUpper pA pB sAB sBC)
    (hu_lower :
      deductionNotBBranchLower pA pB pC sAB sBC ≤
        pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC)
    (hu_upper :
      pA * (1 - sAB) * complementConditionalFromMarginal pB pC sBC ≤
        deductionNotBBranchUpper pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    let itv :=
      deductionCredalStrengthITV pA pB pC sAB sBC hpA hFeas credibility hc
    itv.lower ≤ evidenceSelectedDeductionStrength
      (Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.formulaEvGrade
        (Const := Const) T φ)
      pA pB pC sAB sBC hpA hFeas credibility hc ∧
    evidenceSelectedDeductionStrength
      (Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.formulaEvGrade
        (Const := Const) T φ)
      pA pB pC sAB sBC hpA hFeas credibility hc ≤ itv.upper :=
  evidenceSelectedDeductionStrength_mem_deductionCredalStrengthITV
    (Mettapedia.PLN.Bridges.HOL.BinaryEvidenceReadout.formulaEvGrade
      (Const := Const) T φ)
    pA pB pC sAB sBC hpA hpB_small hFeas h_consist
    ht_lower ht_upper hu_lower hu_upper credibility hc

theorem evidenceSelectedDeductionStrength_crisp_one_eq_formula
    (sideEvidence : BinaryEvidence)
    (hcrisp : (BinaryEvidence.toStrength sideEvidence).toReal = 1)
    (pA pB pC sAB sBC : ℝ)
    (hpA : 0 < pA)
    (hFeas : DeductionBranchFeasibility pA pB pC sAB sBC)
    (credibility : ℝ) (hc : credibility ∈ Set.Icc (0 : ℝ) 1) :
    evidenceSelectedDeductionStrength sideEvidence pA pB pC sAB sBC
      hpA hFeas credibility hc =
      simpleDeductionStrengthFormula pA pB pC sAB sBC := by
  unfold evidenceSelectedDeductionStrength selectedDeductionStrength
  unfold EnvelopeSelector.ofBinaryEvidence EnvelopeSelector.select
  dsimp
  rw [hcrisp]
  ring

/-! ## Phase 3: finite weighted calibration and regret -/

/-- One finite selector-calibration sample.  `x` is the exact side-condition
branch, `y` is the fallback branch, and `latentAssumption` records which branch
was actually valid in the held-out context. -/
structure SelectorSample where
  x : ℝ
  y : ℝ
  latentAssumption : Bool
  x_mem_unit : x ∈ Set.Icc (0 : ℝ) 1
  y_mem_unit : y ∈ Set.Icc (0 : ℝ) 1

namespace SelectorSample

def assumptionIndicator (c : SelectorSample) : ℝ :=
  if c.latentAssumption then 1 else 0

def target (c : SelectorSample) : ℝ :=
  c.y + c.assumptionIndicator * (c.x - c.y)

def prediction (c : SelectorSample) (q : ℝ) : ℝ :=
  c.y + q * (c.x - c.y)

def gapWeight (c : SelectorSample) : ℝ :=
  (c.x - c.y) ^ 2

def loss (c : SelectorSample) (q : ℝ) : ℝ :=
  (c.prediction q - c.target) ^ 2

theorem gapWeight_nonneg (c : SelectorSample) : 0 ≤ c.gapWeight := by
  exact sq_nonneg _

theorem loss_eq_weighted_indicator (c : SelectorSample) (q : ℝ) :
    c.loss q = (q - c.assumptionIndicator) ^ 2 * c.gapWeight := by
  simp [loss, prediction, target, gapWeight]
  ring

end SelectorSample

def sumSquaredLossFixed {n : ℕ} (sample : Fin n → SelectorSample)
    (q : ℝ) : ℝ :=
  ∑ i, (sample i).loss q

def meanSquaredLossFixed {n : ℕ} (sample : Fin n → SelectorSample)
    (q : ℝ) : ℝ :=
  sumSquaredLossFixed sample q / n

/-- Proper fixed-feature calibration target: the estimator `qhat` equals the
conditional probability of the independence side condition under those
features. -/
def calibratedForIndependenceEvent (qhat pS_given_features : ℝ) : Prop :=
  qhat = pS_given_features

/-- Empirical normal equation derived from the squared-loss decomposition for a
fixed feature cell.  The weights `(x-y)^2` are forced by the residual algebra;
this is the sample condition induced by calibration to the independence event,
not a standalone definition of calibration. -/
def empiricalCalibrationCondition {n : ℕ}
    (sample : Fin n → SelectorSample) (q : ℝ) : Prop :=
  q * (∑ i, (sample i).gapWeight) =
    ∑ i, (sample i).assumptionIndicator * (sample i).gapWeight

theorem sumSquaredLossFixed_sub_eq_empiricalCalibrationCondition_gap
    {n : ℕ} (sample : Fin n → SelectorSample) (q r : ℝ)
    (hcal : empiricalCalibrationCondition sample q) :
    sumSquaredLossFixed sample r - sumSquaredLossFixed sample q =
      (r - q) ^ 2 * ∑ i, (sample i).gapWeight := by
  unfold sumSquaredLossFixed
  simp_rw [SelectorSample.loss_eq_weighted_indicator]
  calc
    (∑ i, (r - (sample i).assumptionIndicator) ^ 2 *
          (sample i).gapWeight) -
        ∑ i, (q - (sample i).assumptionIndicator) ^ 2 *
          (sample i).gapWeight
        =
        ∑ i,
          (((r - (sample i).assumptionIndicator) ^ 2 -
              (q - (sample i).assumptionIndicator) ^ 2) *
            (sample i).gapWeight) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ =
        ∑ i,
          ((r - q) *
            ((r + q) * (sample i).gapWeight -
              2 * ((sample i).assumptionIndicator *
                (sample i).gapWeight))) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ =
        (r - q) *
          ((r + q) * (∑ i, (sample i).gapWeight) -
            2 * (∑ i,
              (sample i).assumptionIndicator * (sample i).gapWeight)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ =
        (r - q) *
          ((r + q) * (∑ i, (sample i).gapWeight) -
            2 * (q * ∑ i, (sample i).gapWeight)) := by
          rw [hcal]
    _ = (r - q) ^ 2 * ∑ i, (sample i).gapWeight := by
          ring

theorem empiricalCalibrationCondition_sumSquaredLoss_le_any_fixedWeight
    {n : ℕ} (sample : Fin n → SelectorSample)
    (q r : ℝ)
    (_hq : q ∈ Set.Icc (0 : ℝ) 1)
    (_hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hcal : empiricalCalibrationCondition sample q) :
    sumSquaredLossFixed sample q ≤ sumSquaredLossFixed sample r := by
  have hdiff :=
    sumSquaredLossFixed_sub_eq_empiricalCalibrationCondition_gap
      sample q r hcal
  have hsum_nonneg : 0 ≤ ∑ i, (sample i).gapWeight :=
    Finset.sum_nonneg fun i _ => (sample i).gapWeight_nonneg
  have hprod_nonneg : 0 ≤ (r - q) ^ 2 * ∑ i, (sample i).gapWeight :=
    mul_nonneg (sq_nonneg _) hsum_nonneg
  linarith

theorem empiricalCalibrationCondition_meanSquaredLoss_le_any_fixedWeight
    {n : ℕ} (sample : Fin n → SelectorSample)
    (hn : n ≠ 0)
    (q r : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (hcal : empiricalCalibrationCondition sample q) :
    meanSquaredLossFixed sample q ≤ meanSquaredLossFixed sample r := by
  unfold meanSquaredLossFixed
  have hsum :=
    empiricalCalibrationCondition_sumSquaredLoss_le_any_fixedWeight
      sample q r hq hr hcal
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact div_le_div_of_nonneg_right hsum hn_nonneg

theorem abs_sub_le_width_of_mem_ITV
    (itv : ITV) {x y : ℝ}
    (hx : itv.lower ≤ x ∧ x ≤ itv.upper)
    (hy : itv.lower ≤ y ∧ y ≤ itv.upper) :
    |x - y| ≤ itv.width := by
  rw [abs_sub_le_iff]
  unfold ITV.width
  constructor <;> linarith

theorem selected_abs_error_from_miscalibration_le_width_mul
    (itv : ITV) {q qstar x y : ℝ}
    (_hq : q ∈ Set.Icc (0 : ℝ) 1)
    (_hqstar : qstar ∈ Set.Icc (0 : ℝ) 1)
    (hx : itv.lower ≤ x ∧ x ≤ itv.upper)
    (hy : itv.lower ≤ y ∧ y ≤ itv.upper) :
    |(q * x + (1 - q) * y) -
      (qstar * x + (1 - qstar) * y)| ≤
      itv.width * |q - qstar| := by
  have hxy : |x - y| ≤ itv.width :=
    abs_sub_le_width_of_mem_ITV itv hx hy
  calc
    |(q * x + (1 - q) * y) -
      (qstar * x + (1 - qstar) * y)|
        = |(q - qstar) * (x - y)| := by
          congr 1
          ring
    _ = |q - qstar| * |x - y| := by
          exact abs_mul (q - qstar) (x - y)
    _ ≤ |q - qstar| * itv.width := by
          exact mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    _ = itv.width * |q - qstar| := by ring

/-! ## Phase 4: mediation-chain fixtures -/

def toyPositiveFeasibility :
    DeductionBranchFeasibility (1/2 : ℝ) (1/2 : ℝ) (1/2 : ℝ)
      (9/10 : ℝ) (9/10 : ℝ) where
  AB_nonneg := by norm_num [deductionJointAB]
  AB_le_B := by norm_num [deductionJointAB]
  BC_nonneg := by norm_num [deductionJointBC]
  BC_le_B := by norm_num [deductionJointBC]
  AnotB_nonneg := by norm_num [deductionJointAB]
  AnotB_le_notB := by norm_num [deductionJointAB]
  CnotB_nonneg := by norm_num [deductionJointBC]
  CnotB_le_notB := by norm_num [deductionJointBC]

def toyNegativeFeasibility :
    DeductionBranchFeasibility (1/10 : ℝ) (1/2 : ℝ) (9/20 : ℝ)
      (9/10 : ℝ) (9/10 : ℝ) where
  AB_nonneg := by norm_num [deductionJointAB]
  AB_le_B := by norm_num [deductionJointAB]
  BC_nonneg := by norm_num [deductionJointBC]
  BC_le_B := by norm_num [deductionJointBC]
  AnotB_nonneg := by norm_num [deductionJointAB]
  AnotB_le_notB := by norm_num [deductionJointAB]
  CnotB_nonneg := by norm_num [deductionJointBC]
  CnotB_le_notB := by norm_num [deductionJointBC]

def toyPositiveITV : ITV :=
  deductionCredalStrengthITV (1/2 : ℝ) (1/2 : ℝ) (1/2 : ℝ)
    (9/10 : ℝ) (9/10 : ℝ) (by norm_num) toyPositiveFeasibility
    (19/20 : ℝ) (by norm_num)

def toyNegativeITV : ITV :=
  deductionCredalStrengthITV (1/10 : ℝ) (1/2 : ℝ) (9/20 : ℝ)
    (9/10 : ℝ) (9/10 : ℝ) (by norm_num) toyNegativeFeasibility
    (1/10 : ℝ) (by norm_num)

def toyPositivePoint : ℝ :=
  simpleDeductionStrengthFormula (1/2 : ℝ) (1/2 : ℝ) (1/2 : ℝ)
    (9/10 : ℝ) (9/10 : ℝ)

def toyNegativePoint : ℝ :=
  simpleDeductionStrengthFormula (1/10 : ℝ) (1/2 : ℝ) (9/20 : ℝ)
    (9/10 : ℝ) (9/10 : ℝ)

def toyPositiveSideEvidence : BinaryEvidence where
  pos := 19
  neg := 1

def toyNegativeSideEvidence : BinaryEvidence where
  pos := 1
  neg := 9

def toyPositiveSelected : ℝ :=
  evidenceSelectedDeductionStrength toyPositiveSideEvidence
    (1/2 : ℝ) (1/2 : ℝ) (1/2 : ℝ) (9/10 : ℝ) (9/10 : ℝ)
    (by norm_num) toyPositiveFeasibility (19/20 : ℝ) (by norm_num)

def toyNegativeSelected : ℝ :=
  evidenceSelectedDeductionStrength toyNegativeSideEvidence
    (1/10 : ℝ) (1/2 : ℝ) (9/20 : ℝ) (9/10 : ℝ) (9/10 : ℝ)
    (by norm_num) toyNegativeFeasibility (1/10 : ℝ) (by norm_num)

theorem toyPositiveSideEvidence_toStrength :
    (BinaryEvidence.toStrength toyPositiveSideEvidence).toReal = 19 / 20 := by
  rw [toReal_toStrength_eq_pos_div_total]
  · norm_num [toyPositiveSideEvidence, BinaryEvidence.total]
  · norm_num [toyPositiveSideEvidence, BinaryEvidence.total]

theorem toyNegativeSideEvidence_toStrength :
    (BinaryEvidence.toStrength toyNegativeSideEvidence).toReal = 1 / 10 := by
  rw [toReal_toStrength_eq_pos_div_total]
  · norm_num [toyNegativeSideEvidence, BinaryEvidence.total]
  · norm_num [toyNegativeSideEvidence, BinaryEvidence.total]

theorem toyPositive_consistency :
    conditionalProbabilityConsistency (1/2 : ℝ) (1/2 : ℝ) (9/10 : ℝ) ∧
      conditionalProbabilityConsistency (1/2 : ℝ) (1/2 : ℝ) (9/10 : ℝ) := by
  norm_num [conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability]

theorem toyNegative_consistency :
    conditionalProbabilityConsistency (1/10 : ℝ) (1/2 : ℝ) (9/10 : ℝ) ∧
      conditionalProbabilityConsistency (1/2 : ℝ) (9/20 : ℝ) (9/10 : ℝ) := by
  norm_num [conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability]

theorem toyPositiveITV_lower_eq : toyPositiveITV.lower = 4 / 5 := by
  norm_num [toyPositiveITV, deductionCredalStrengthITV,
    deductionCredalStrengthLower, deductionCredalJointLower,
    deductionBBranchLower, deductionNotBBranchLower, deductionJointAB,
    deductionJointBC]

theorem toyPositiveITV_upper_eq : toyPositiveITV.upper = 1 := by
  norm_num [toyPositiveITV, deductionCredalStrengthITV,
    deductionCredalStrengthUpper, deductionCredalJointUpper,
    deductionBBranchUpper, deductionNotBBranchUpper, deductionJointAB,
    deductionJointBC]

theorem toyPositivePoint_eq : toyPositivePoint = 41 / 50 := by
  norm_num [toyPositivePoint, simpleDeductionStrengthFormula,
    conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability]

theorem toyPositiveSelected_eq : toyPositiveSelected = 103 / 125 := by
  unfold toyPositiveSelected evidenceSelectedDeductionStrength
    selectedDeductionStrength EnvelopeSelector.select
  change
    (BinaryEvidence.toStrength toyPositiveSideEvidence).toReal *
        simpleDeductionStrengthFormula (1 / 2) (1 / 2) (1 / 2) (9 / 10) (9 / 10) +
      (1 - (BinaryEvidence.toStrength toyPositiveSideEvidence).toReal) *
        (deductionCredalStrengthITV (1 / 2) (1 / 2) (1 / 2) (9 / 10) (9 / 10)
          (by norm_num) toyPositiveFeasibility (19 / 20) (by norm_num)).strength =
      103 / 125
  rw [toyPositiveSideEvidence_toStrength]
  norm_num [simpleDeductionStrengthFormula, conditionalProbabilityConsistency,
    smallestIntersectionProbability, largestIntersectionProbability,
    deductionCredalStrengthITV, ITV.strength, deductionCredalStrengthLower,
    deductionCredalStrengthUpper, deductionCredalJointLower,
    deductionCredalJointUpper, deductionBBranchLower, deductionBBranchUpper,
    deductionNotBBranchLower, deductionNotBBranchUpper, deductionJointAB,
    deductionJointBC]

theorem toyPositiveSelected_mem_ITV :
    toyPositiveITV.lower ≤ toyPositiveSelected ∧
      toyPositiveSelected ≤ toyPositiveITV.upper := by
  rw [toyPositiveITV_lower_eq, toyPositiveITV_upper_eq, toyPositiveSelected_eq]
  norm_num

theorem toyNegativeITV_lower_eq : toyNegativeITV.lower = 2 / 5 := by
  norm_num [toyNegativeITV, deductionCredalStrengthITV,
    deductionCredalStrengthLower, deductionCredalJointLower,
    deductionBBranchLower, deductionNotBBranchLower, deductionJointAB,
    deductionJointBC]

theorem toyNegativeITV_upper_eq : toyNegativeITV.upper = 9 / 10 := by
  norm_num [toyNegativeITV, deductionCredalStrengthITV,
    deductionCredalStrengthUpper, deductionCredalJointUpper,
    deductionBBranchUpper, deductionNotBBranchUpper, deductionJointAB,
    deductionJointBC]

theorem toyNegativeITV_width_eq : toyNegativeITV.width = 1 / 2 := by
  rw [ITV.width, toyNegativeITV_lower_eq, toyNegativeITV_upper_eq]
  norm_num

theorem toyNegativePoint_eq : toyNegativePoint = 81 / 100 := by
  norm_num [toyNegativePoint, simpleDeductionStrengthFormula,
    conditionalProbabilityConsistency, smallestIntersectionProbability,
    largestIntersectionProbability]

theorem toyNegativeSelected_eq : toyNegativeSelected = 333 / 500 := by
  unfold toyNegativeSelected evidenceSelectedDeductionStrength
    selectedDeductionStrength EnvelopeSelector.select
  change
    (BinaryEvidence.toStrength toyNegativeSideEvidence).toReal *
        simpleDeductionStrengthFormula (1 / 10) (1 / 2) (9 / 20) (9 / 10) (9 / 10) +
      (1 - (BinaryEvidence.toStrength toyNegativeSideEvidence).toReal) *
        (deductionCredalStrengthITV (1 / 10) (1 / 2) (9 / 20) (9 / 10) (9 / 10)
          (by norm_num) toyNegativeFeasibility (1 / 10) (by norm_num)).strength =
      333 / 500
  rw [toyNegativeSideEvidence_toStrength]
  norm_num [simpleDeductionStrengthFormula, conditionalProbabilityConsistency,
    smallestIntersectionProbability, largestIntersectionProbability,
    deductionCredalStrengthITV, ITV.strength, deductionCredalStrengthLower,
    deductionCredalStrengthUpper, deductionCredalJointLower,
    deductionCredalJointUpper, deductionBBranchLower, deductionBBranchUpper,
    deductionNotBBranchLower, deductionNotBBranchUpper, deductionJointAB,
    deductionJointBC]

/-- The negative fixture is not a point-escaping-envelope example: the point
formula remains in the interval.  It is point-far-from-true-conditional: the
certified interval allows a true value as low as the lower endpoint `2/5`, while
the naive point reports `81/100`. -/
theorem toyNegativePoint_mem_ITV :
    toyNegativeITV.lower ≤ toyNegativePoint ∧
      toyNegativePoint ≤ toyNegativeITV.upper := by
  rw [toyNegativeITV_lower_eq, toyNegativeITV_upper_eq, toyNegativePoint_eq]
  norm_num

theorem toyNegativePoint_ne_lowerEndpoint :
    toyNegativePoint ≠ 2 / 5 := by
  rw [toyNegativePoint_eq]
  norm_num

theorem toyNegativePoint_minus_lowerEndpoint_eq :
    toyNegativePoint - (2 / 5 : ℝ) = 41 / 100 := by
  rw [toyNegativePoint_eq]
  norm_num

theorem toyNegativeLowerEndpoint_mem_ITV :
    toyNegativeITV.lower ≤ (2 / 5 : ℝ) ∧
      (2 / 5 : ℝ) ≤ toyNegativeITV.upper := by
  rw [toyNegativeITV_lower_eq, toyNegativeITV_upper_eq]
  norm_num

theorem toyNegativeSelected_mem_ITV :
    toyNegativeITV.lower ≤ toyNegativeSelected ∧
      toyNegativeSelected ≤ toyNegativeITV.upper := by
  rw [toyNegativeITV_lower_eq, toyNegativeITV_upper_eq, toyNegativeSelected_eq]
  norm_num

end

end Mettapedia.PLN.InferenceControl.CertifiedChaining.EstimatorEnvelope
