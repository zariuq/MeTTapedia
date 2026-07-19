import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.BeliefState

/-!
# Expressivity boundary of hardwired natural-coordinate fusion

This file compares a scalar learned interpolation cell with the existing
precision-addition belief update.  All results are finite-dimensional scalar
linear-Gaussian algebra.  They make no claim about nonlinear trained cells.

If observation precision may vary, hardwired fusion realizes exactly the
finite gate interval `[0,1)`.  With prior and observation calibration fixed,
the hardwired gate is a single point.  Larger learned gates correspond exactly
to decaying old precision, with zero retained precision giving overwrite.
Smaller gates instead discount the new observation; they are recorded as a
separate calibration freedom rather than mislabeled as forgetting.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Set

/-! ## CAROM interpolation and the WM inclusion -/

/-- Scalar learned mixing cell used for the linear CAROM comparison. -/
noncomputable def caromMix (oldValue candidate gate : ℝ) : ℝ :=
  oldValue + gate * (candidate - oldValue)

/-- The counts/information-fusion moment chart is literally a CAROM update. -/
theorem precisionInterpolate_eq_caromMix
    (oldValue candidate priorPrecision observationPrecision : ℝ) :
    precisionInterpolate oldValue candidate
        priorPrecision observationPrecision =
      caromMix oldValue candidate
        (precisionGain priorPrecision observationPrecision) :=
  rfl

/-- A finite CAROM gate is precision-valid when some nonnegative observation
precision realizes it against the fixed positive prior precision. -/
def PrecisionValidGate (priorPrecision gate : ℝ) : Prop :=
  ∃ observationPrecision : ℝ,
    0 ≤ observationPrecision ∧
      gate = precisionGain priorPrecision observationPrecision

/-- Exact WM-to-CAROM inclusion and complement: against a positive finite
prior precision, natural-coordinate addition realizes precisely `[0,1)`.
The endpoint `1` would require discarding all finite prior evidence. -/
theorem precisionValidGate_iff_mem_Ico
    (priorPrecision gate : ℝ) (hprior : 0 < priorPrecision) :
    PrecisionValidGate priorPrecision gate ↔ gate ∈ Ico (0 : ℝ) 1 := by
  constructor
  · rintro ⟨observationPrecision, hobservation, rfl⟩
    have hsum : 0 < priorPrecision + observationPrecision :=
      add_pos_of_pos_of_nonneg hprior hobservation
    constructor
    · unfold precisionGain
      exact div_nonneg hobservation hsum.le
    · unfold precisionGain
      rw [div_lt_one hsum]
      linarith
  · intro hgate
    have hden : 0 < 1 - gate := sub_pos.mpr hgate.2
    let observationPrecision := priorPrecision * gate / (1 - gate)
    have hobservation : 0 ≤ observationPrecision := by
      dsimp [observationPrecision]
      exact div_nonneg (mul_nonneg hprior.le hgate.1) hden.le
    refine ⟨observationPrecision, hobservation, ?_⟩
    unfold precisionGain
    dsimp [observationPrecision]
    field_simp [hprior.ne', hden.ne']
    ring

/-- Positive observation precision produces a strictly interior learned gate. -/
theorem precisionGain_mem_Ioo
    (priorPrecision observationPrecision : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision) :
    precisionGain priorPrecision observationPrecision ∈ Ioo (0 : ℝ) 1 := by
  have hsum : 0 < priorPrecision + observationPrecision :=
    add_pos hprior hobservation
  constructor
  · unfold precisionGain
    exact div_pos hobservation hsum
  · unfold precisionGain
    rw [div_lt_one hsum]
    linarith

/-! ## Fixed-calibration non-conservative gates -/

/-- Gain after retaining only `decay` times the old precision while preserving
the calibrated observation precision. -/
noncomputable def decayedPriorGain
    (priorPrecision observationPrecision decay : ℝ) : ℝ :=
  observationPrecision / (decay * priorPrecision + observationPrecision)

/-- No decay recovers hardwired natural-coordinate addition. -/
theorem decayedPriorGain_one
    (priorPrecision observationPrecision : ℝ) :
    decayedPriorGain priorPrecision observationPrecision 1 =
      precisionGain priorPrecision observationPrecision := by
  simp [decayedPriorGain, precisionGain]

/-- Exact representation of the upward CAROM extension: with both precisions
positive, gates between the calibrated hardwired gate and overwrite are
exactly those obtained by retaining a fraction `decay ∈ [0,1]` of old
precision. -/
theorem mem_hardwiredGate_Icc_one_iff_exists_decay
    (priorPrecision observationPrecision gate : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision) :
    gate ∈ Icc (precisionGain priorPrecision observationPrecision) 1 ↔
      ∃ decay ∈ Icc (0 : ℝ) 1,
        gate = decayedPriorGain
          priorPrecision observationPrecision decay := by
  have hsum : 0 < priorPrecision + observationPrecision :=
    add_pos hprior hobservation
  constructor
  · intro hgate
    have hbaseline : 0 < precisionGain priorPrecision observationPrecision :=
      (precisionGain_mem_Ioo priorPrecision observationPrecision
        hprior hobservation).1
    have hgatePos : 0 < gate := hbaseline.trans_le hgate.1
    let decay := observationPrecision * (1 - gate) /
      (priorPrecision * gate)
    have hdecayNonneg : 0 ≤ decay := by
      dsimp [decay]
      exact div_nonneg
        (mul_nonneg hobservation.le (sub_nonneg.mpr hgate.2))
        (mul_nonneg hprior.le hgatePos.le)
    have hcross : observationPrecision ≤
        gate * (priorPrecision + observationPrecision) := by
      rw [← div_le_iff₀ hsum]
      simpa [precisionGain] using hgate.1
    have hdecayLe : decay ≤ 1 := by
      dsimp [decay]
      rw [div_le_one (mul_pos hprior hgatePos)]
      nlinarith
    refine ⟨decay, ⟨hdecayNonneg, hdecayLe⟩, ?_⟩
    unfold decayedPriorGain
    dsimp [decay]
    have hden : 0 < priorPrecision * gate := mul_pos hprior hgatePos
    have hfusionDen : 0 <
        (observationPrecision * (1 - gate) /
            (priorPrecision * gate)) * priorPrecision +
          observationPrecision := by
      exact add_pos_of_nonneg_of_pos (mul_nonneg hdecayNonneg hprior.le)
        hobservation
    field_simp [hden.ne', hfusionDen.ne']
    ring
  · rintro ⟨decay, hdecay, rfl⟩
    have hdecayedSum : 0 <
        decay * priorPrecision + observationPrecision :=
      add_pos_of_nonneg_of_pos (mul_nonneg hdecay.1 hprior.le) hobservation
    constructor
    · rw [precisionGain, decayedPriorGain]
      rw [div_le_div_iff₀ hsum hdecayedSum]
      have hscaled : decay * priorPrecision ≤ priorPrecision := by
        nlinarith [mul_le_mul_of_nonneg_right hdecay.2 hprior.le]
      nlinarith
    · rw [decayedPriorGain, div_le_one hdecayedSum]
      nlinarith [mul_nonneg hdecay.1 hprior.le]

/-- At fixed positive calibration, complete decay is exactly overwrite. -/
theorem decayedPriorGain_eq_one_iff
    (priorPrecision observationPrecision decay : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision)
    (hdecay : 0 ≤ decay) :
    decayedPriorGain priorPrecision observationPrecision decay = 1 ↔
      decay = 0 := by
  have hsum : 0 < decay * priorPrecision + observationPrecision :=
    add_pos_of_nonneg_of_pos (mul_nonneg hdecay hprior.le) hobservation
  constructor
  · intro h
    unfold decayedPriorGain at h
    rw [div_eq_one_iff_eq hsum.ne'] at h
    nlinarith
  · rintro rfl
    simp [decayedPriorGain, hobservation.ne']

/-- Exact complement inside the upward learned-gate family: a gate differs
from hardwired fusion iff it uses strict evidence decay; decay zero is the
overwrite endpoint by `decayedPriorGain_eq_one_iff`. -/
theorem upwardCAROM_not_hardwired_iff_strictDecay
    (priorPrecision observationPrecision gate : ℝ)
    (hprior : 0 < priorPrecision) (hobservation : 0 < observationPrecision)
    (hgate : gate ∈ Icc
      (precisionGain priorPrecision observationPrecision) 1) :
    gate ≠ precisionGain priorPrecision observationPrecision ↔
      ∃ decay ∈ Ico (0 : ℝ) 1,
        gate = decayedPriorGain
          priorPrecision observationPrecision decay := by
  constructor
  · intro hne
    obtain ⟨decay, hdecay, hrepr⟩ :=
      (mem_hardwiredGate_Icc_one_iff_exists_decay
        priorPrecision observationPrecision gate hprior hobservation).mp hgate
    refine ⟨decay, ⟨hdecay.1, ?_⟩, hrepr⟩
    by_contra hnot
    have hone : decay = 1 := le_antisymm hdecay.2 (le_of_not_gt hnot)
    apply hne
    rw [hrepr, hone, decayedPriorGain_one]
  · rintro ⟨decay, hdecay, rfl⟩ heq
    unfold decayedPriorGain precisionGain at heq
    have hsum₁ : 0 < decay * priorPrecision + observationPrecision :=
      add_pos_of_nonneg_of_pos (mul_nonneg hdecay.1 hprior.le) hobservation
    have hsum₂ : 0 < priorPrecision + observationPrecision :=
      add_pos hprior hobservation
    field_simp [hsum₁.ne', hsum₂.ne'] at heq
    have : decay = 1 := by nlinarith
    exact (ne_of_lt hdecay.2) this

/-! ## The lower-gate calibration boundary -/

/-- Gates below the calibrated hardwired gain discount the new observation.
This is a distinct learned freedom from old-evidence forgetting. -/
def ObservationDiscountGate
    (priorPrecision observationPrecision gate : ℝ) : Prop :=
  0 ≤ gate ∧ gate < precisionGain priorPrecision observationPrecision

/-- Unit-interval CAROM gates have an exact four-way classification relative
to fixed calibration: observation discount, hardwired fusion, partial prior
forgetting, or overwrite. -/
theorem caromUnitGate_fixedCalibration_partition
    (priorPrecision observationPrecision gate : ℝ)
    (hgate : gate ∈ Icc (0 : ℝ) 1) :
    ObservationDiscountGate priorPrecision observationPrecision gate ∨
      gate = precisionGain priorPrecision observationPrecision ∨
      (precisionGain priorPrecision observationPrecision < gate ∧ gate < 1) ∨
      gate = 1 := by
  rcases lt_trichotomy gate
      (precisionGain priorPrecision observationPrecision) with hlt | heq | hgt
  · exact Or.inl ⟨hgate.1, hlt⟩
  · exact Or.inr (Or.inl heq)
  · by_cases hone : gate = 1
    · exact Or.inr (Or.inr (Or.inr hone))
    · exact Or.inr (Or.inr (Or.inl ⟨hgt, lt_of_le_of_ne hgate.2 hone⟩))

/-! ## Positive and negative fixtures -/

/-- Equal precisions embed hardwired fusion as the CAROM half-gate. -/
theorem hardwiredFusion_is_carom_positiveExample :
    precisionInterpolate 0 1 1 1 = caromMix 0 1 (1 / 2) := by
  norm_num [precisionInterpolate, precisionGain, caromMix]

/-- Finite natural-coordinate addition cannot overwrite a positive-precision
prior, even though a unit CAROM gate can. -/
theorem overwrite_not_precisionValid_negativeExample :
    ¬PrecisionValidGate 1 1 := by
  rw [precisionValidGate_iff_mem_Ico 1 1 (by norm_num)]
  norm_num

#print axioms precisionInterpolate_eq_caromMix
#print axioms precisionValidGate_iff_mem_Ico
#print axioms mem_hardwiredGate_Icc_one_iff_exists_decay
#print axioms upwardCAROM_not_hardwired_iff_strictDecay
#print axioms caromUnitGate_fixedCalibration_partition
#print axioms hardwiredFusion_is_carom_positiveExample
#print axioms overwrite_not_precisionValid_negativeExample

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
